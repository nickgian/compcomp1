(*First, construct the two effect semantics*)
Require Import Coqlib.
Require Import Values.
Require Import Memory.
Require Export Axioms.
Require Import Errors.
Require Import Events.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Export Maps.
Require Import Csharpminor.
Require Import Cminor.
Require Import Cminorgen.

Require Import mem_lemmas.
Require Import semantics.
Require Import semantics_lemmas.
Require Import effect_semantics.
Require Import structured_injections.
Require Import reach.
Require Import simulations.
Require Import effect_properties.
Require Import simulations_lemmas.

Require Import Cminor_coop.
Require Import Cminor_eff.
Require Import Csharpminor_coop.
Require Import Csharpminor_eff.

Require Import CminorgenproofRestructured.
Require Import CminorgenproofSIM.

Require Import Coq.Program.Equality.
Require Import BuiltinEffects.

Section TRANSLATION.
Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

(*NEW*) Variable hf : I64Helpers.helper_functions.
    
Lemma match_globalenvs_init':
  forall (R: list_norepet (map fst (prog_defs prog)))
  m j,
  Genv.init_mem prog = Some m ->
  meminj_preserves_globals ge j ->
  match_globalenvs prog j (Mem.nextblock m).
Proof.
  intros. 
  destruct H0 as [A [B C]].
  constructor. 
  intros b D. intros [[id E]|[[gv E]|[fptr E]]]; eauto.
  cut (exists id, Genv.find_symbol (Genv.globalenv prog) id = Some b).
  intros [id ID].
  solve[eapply A; eauto].
  eapply valid_init_is_global; eauto.
  intros. symmetry. solve[eapply (C _ _ _ _ H0); eauto].
  intros. eapply Genv.find_symbol_not_fresh; eauto.
  intros. eapply Genv.find_funct_ptr_not_fresh ; eauto.
  intros. eapply Genv.find_var_info_not_fresh; eauto. 
Qed.

Lemma GDE_lemma: genvs_domain_eq ge tge.
Proof.
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros.
     split; intros; destruct H as [id Hid].
      rewrite <- (symbols_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
      rewrite (symbols_preserved _ _ TRANSL) in Hid.
      exists id; assumption.
     split; intros b. 
       split; intros; destruct H as [id Hid].
       rewrite <- (varinfo_preserved _ _ TRANSL) in Hid.
       exists id; assumption.
       rewrite (varinfo_preserved _ _ TRANSL) in Hid.
       exists id; assumption.
    intros. split.
      intros [f H].
        apply (function_ptr_translated _ _ TRANSL) in H. 
        destruct H as [? [? ?]].
        eexists; eassumption.
     intros [f H]. unfold transl_program in TRANSL. 
         apply (@Genv.find_funct_ptr_rev_transf_partial
           _ _ _ transl_fundef prog _ TRANSL) in H. 
         destruct H as [? [? _]]. eexists; eassumption.
Qed.

Let core_data := CSharpMin_core.

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (sp: Values.block)
                 (lo hi: Values.block) : Prop :=
  mk_match_env {

(** C#minor local variables match sub-blocks of the Cminor stack data block. *)
    me_vars:
      forall id, match_var f sp (e!id) (cenv!id);

(** [lo, hi] is a proper interval. *)
    me_low_high:
      Ple lo hi;

(** Every block appearing in the C#minor environment [e] must be
  in the range [lo, hi]. *)
    me_bounded:
      forall id b sz, PTree.get id e = Some(b, sz) -> Ple lo b /\ Plt b hi;

(** All blocks mapped to sub-blocks of the Cminor stack data must be
    images of variables from the C#minor environment [e] *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists sz, PTree.get id e = Some(b, sz)


(*LENB: MOVED TO structured_match_callstack below
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> Plt b lo -> Plt tb sp*)
  }.

Ltac geninv x := 
  let H := fresh in (generalize x; intro H; inv H).

Lemma match_env_invariant:
  forall f1 cenv e sp lo hi f2,
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  (forall b delta, f2 b = Some(sp, delta) -> f1 b = Some(sp, delta)) ->
  (forall b, Plt b lo -> f2 b = f1 b) ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. destruct H. constructor; auto.
(* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
(* bounded *)
  intros. eauto. 
(* below 
  intros. rewrite H2 in H; eauto.*)
Qed.

Lemma match_env_restrict_invariant:
  forall f1 cenv e sp lo hi f2 (WD1: SM_wd f1) (WD2: SM_wd f2)
  (ME: match_env (restrict (as_inj f1) (vis f1)) cenv e sp lo hi)
  (INT: intern_incr f1 f2)
  (HA: forall b delta, as_inj f2 b = Some(sp, delta) -> 
                       as_inj f1 b = Some(sp, delta))
  (HB: forall b, Plt b lo -> (as_inj f2)  b = (as_inj f1) b),
  match_env (restrict (as_inj f2) (vis f2)) cenv e sp lo hi.
Proof. intros.
  assert (INC:= intern_incr_restrict _ _ WD2 INT).
  eapply match_env_invariant; eauto.
    intros. 
      destruct (restrictD_Some _ _ _ _ _ H); clear H.
      assert (AI:  as_inj f1 b = Some (sp, delta)).
        eapply (HA _ _ H0). (*xomega.*)
      eapply restrictI_Some; try eassumption.
      eapply intern_incr_vis_inv; try eassumption.
   intros. 
      remember (restrict (as_inj f1) (vis f1) b) as d.
      destruct d; apply eq_sym in Heqd.
        destruct p.
        eapply INC; eassumption.
      remember (restrict (as_inj f2) (vis f2) b) as q.
      destruct q; trivial; apply eq_sym in Heqq.
        destruct p.
        destruct (restrictD_Some _ _ _ _ _ Heqq); clear Heqq.
        rewrite HB in H0.
          unfold restrict in Heqd.
          rewrite (intern_incr_vis_inv _ _ WD1 WD2 INT _ _ _ H0 H1) in Heqd.
            congruence. 
          xomega. 
Qed.

Remark inject_incr_separated_same:
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b, Mem.valid_block m1 b -> f2 b = f1 b.
Proof.
  intros. case_eq (f1 b).
  intros [b' delta] EQ. apply H; auto. 
  intros EQ. case_eq (f2 b).
  intros [b'1 delta1] EQ1. exploit H0; eauto. intros [C D]. contradiction.
  auto.
Qed.

Remark inject_incr_separated_same':
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b b' delta,
  f2 b = Some(b', delta) -> Mem.valid_block m1' b' -> f1 b = Some(b', delta).
Proof.
  intros. case_eq (f1 b).
  intros [b'1 delta1] EQ. exploit H; eauto. congruence.
  intros. exploit H0; eauto. intros [C D]. contradiction.
Qed.

Lemma padding_freeable_invariant:
  forall f1 e tm1 sp sz cenv lo hi f2 tm2,
  padding_freeable f1 e tm1 sp sz ->
  match_env f1 cenv e sp lo hi ->
  (forall ofs, Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b hi -> f2 b = f1 b) ->
  padding_freeable f2 e tm2 sp sz.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [A | A].
  left; auto.
  right. inv A. exploit me_bounded; eauto. intros [D E].
  econstructor; eauto. rewrite H2; auto. 
Qed.

Lemma match_env_external_call:
  forall f1 cenv e sp lo hi f2 m1 m1' (WD2: SM_wd f2),
  match_env (restrict (as_inj f1) (vis f1)) cenv e sp lo hi ->
  extern_incr f1 f2 ->
  inject_separated (restrict (as_inj f1) (vis f1)) (as_inj f2) m1 m1' ->
  Ple hi (Mem.nextblock m1) -> Plt sp (Mem.nextblock m1') ->
   match_env (as_inj f2) cenv e sp lo hi.
Proof.
  intros. 
  inv H.
  econstructor; try eassumption; intros.
    specialize (me_vars0 id).
      inv me_vars0. inv H5.
      constructor; econstructor; try eassumption.
      destruct (restrictD_Some _ _ _ _ _ H9).
      eapply (extern_incr_as_inj _ _ H0); assumption.
     constructor.
   remember (restrict (as_inj f1) (vis f1) b) as d.
     destruct d; apply  eq_sym in Heqd.
       destruct p.
       destruct (restrictD_Some _ _ _ _ _ Heqd).
       apply extern_incr_as_inj in H0.
         rewrite (H0 _ _ _ H4) in H. inv H.
       apply (me_inv0 _ _ Heqd).
       assumption.
     destruct (H1 _ _ _ Heqd H).
       elim H5. apply H3.
Qed.

Inductive structured_match_callstack mu (m: mem) (tm: mem):
                          callstack -> Values.block -> Values.block -> Prop :=
  | st_mcs_nil:
      forall hi bound tbound,
      match_globalenvs prog (restrict (as_inj mu) (vis mu)) hi ->
      Ple hi bound -> Ple hi tbound ->
      structured_match_callstack mu m tm nil bound tbound 
  | st_mcs_cons:
      forall cenv tf e le te sp lo hi cs bound tbound
        (BOUND: Ple hi bound)
        (TBOUND: Plt sp tbound)
        (MTMP: match_temps (restrict (as_inj mu) (vis mu)) le te)
        (MENV: match_env (restrict (as_inj mu) (vis mu)) cenv e sp lo hi)
        (BOUND: match_bounds e m)
        (PERM: padding_freeable (restrict (as_inj mu) (vis mu)) e tm sp tf.(fn_stackspace))
        (SPlocal: locBlocksTgt mu sp = true) (*NEW*)

        (*LENB: Here is the condition me_incr from match_env above,
           but we assert it only for local_of*)
        (ME_INCR: forall b tb delta,
               (local_of mu) b = Some(tb, delta) -> Plt b lo -> Plt tb sp)
        (MCS: structured_match_callstack mu m tm cs lo sp),
      structured_match_callstack mu m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound.

Lemma structured_match_callstack_incr_bound:
  forall f m tm cs bound tbound bound' tbound',
  structured_match_callstack f m tm cs bound tbound ->
  Ple bound bound' -> Ple tbound tbound' ->
  structured_match_callstack f m tm cs bound' tbound'.
Proof.
  intros. inv H.
  econstructor; eauto. xomega. xomega. 
  constructor; auto. xomega. xomega.
Qed.

Lemma structured_match_callstack_intern_invariant:
  forall f1 m1 tm1 f2 m2 tm2 cs bound tbound (WD1: SM_wd f1) (WD2: SM_wd f2),
  intern_incr f1 f2 ->
  structured_match_callstack f1 m1 tm1 cs bound tbound ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall sp ofs, Plt sp tbound -> Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b bound -> (as_inj f2) b = (as_inj f1) b) ->
  (forall b b' delta, (as_inj f2) b = Some(b', delta) -> Plt b' tbound -> (as_inj f1) b = Some(b', delta)) ->
  structured_match_callstack f2 m2 tm2 cs bound tbound.
Proof. intros f1 m1 tm1 f2 m2 tm2 cs bound tbound WD1 WD2 IntInc.
  assert (INC:= intern_incr_restrict _ _ WD2 IntInc). 
  induction 1; intros.
  (* base case *)
  econstructor; eauto.
  inv H. constructor; intros; eauto.
  eapply IMAGE; eauto. 
    destruct (restrictD_Some _ _ _ _ _ H6); clear H6.
    assert (AI:  as_inj f1 b1 = Some (b2, delta)).
      eapply (H5 _ _ _ H8). xomega.
    eapply restrictI_Some; try eassumption.
    eapply intern_incr_vis_inv; eassumption.
  (* inductive case *)
  assert (Ple lo hi) by (eapply me_low_high; eauto).
  econstructor; eauto.
  eapply match_temps_invariant; eauto.
  eapply match_env_restrict_invariant with (f1:=f1); try eassumption.
    intros. apply H3. assumption. assumption.
    intros. apply H2. xomega.
  eapply match_bounds_invariant; eauto.
    intros. eapply H0; eauto. 
    exploit me_bounded; eauto. xomega. 
  eapply padding_freeable_invariant; eauto. 
    intros. 
      remember (restrict (as_inj f1) (vis f1) b) as d.
      destruct d; apply eq_sym in Heqd.
        destruct p.
        eapply INC; eassumption.
      remember (restrict (as_inj f2) (vis f2) b) as q.
      destruct q; trivial; apply eq_sym in Heqq.
        destruct p.
        destruct (restrictD_Some _ _ _ _ _ Heqq); clear Heqq.
        rewrite H2 in H6.
          unfold restrict in Heqd.
          rewrite (intern_incr_vis_inv _ _ WD1 WD2 IntInc _ _ _ H6 H7) in Heqd.
            congruence. 
          xomega.
  eapply IntInc. assumption.
  intros. exploit (H2 b). xomega. unfold as_inj, join. rewrite H5.
            destruct (disjoint_extern_local _ WD2 b).
              assert (extern_of f1 = extern_of f2) by eapply IntInc. 
              rewrite H8, H7. 
              intros. apply eq_sym in H9. 
              apply (ME_INCR _ _ _ H9 H6). 
           rewrite H7 in H5; discriminate. 
  eapply IHstructured_match_callstack; eauto. 
    intros. eapply H0; eauto. xomega. 
    intros. eapply H2; eauto. xomega. 
Qed.

Lemma structured_match_callstack_builtin_invariant:
  forall f1 m1 tm1 f2 m2 tm2 cs bound tbound (WD1: SM_wd f1) (WD2: SM_wd f2),
  intern_incr f1 f2 ->
  structured_match_callstack f1 m1 tm1 cs bound tbound ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (Mem.unchanged_on (loc_out_of_reach (restrict (as_inj f1) (vis f1)) m1) tm1 tm2) ->
  (forall b, Plt b bound -> (as_inj f2) b = (as_inj f1) b) ->
  (forall b b' delta, (as_inj f2) b = Some(b', delta) -> Plt b' tbound -> (as_inj f1) b = Some(b', delta)) ->
  structured_match_callstack f2 m2 tm2 cs bound tbound.
Proof. intros f1 m1 tm1 f2 m2 tm2 cs bound tbound WD1 WD2 IntInc.
  assert (INC:= intern_incr_restrict _ _ WD2 IntInc). 
  induction 1; intros.
  (* base case *)
  econstructor; eauto.
  inv H. constructor; intros; eauto.
  eapply IMAGE; eauto. 
    destruct (restrictD_Some _ _ _ _ _ H6); clear H6.
    assert (AI:  as_inj f1 b1 = Some (b2, delta)).
      eapply (H5 _ _ _ H8). xomega.
    eapply restrictI_Some; try eassumption.
    eapply intern_incr_vis_inv; eassumption.
  (* inductive case *)
  assert (Ple lo hi) by (eapply me_low_high; eauto).
  econstructor; eauto.
  eapply match_temps_invariant; eauto.
  eapply match_env_restrict_invariant with (f1:=f1); try eassumption.
    intros. apply H3. assumption. assumption.
    intros. apply H2. xomega.
  eapply match_bounds_invariant; eauto.
    intros. eapply H0; eauto. 
    exploit me_bounded; eauto. xomega.
  (* padding-freeable *)
  clear IHstructured_match_callstack.
  { red; intros.
    destruct (is_reachable_from_env_dec (restrict (as_inj f1) (vis f1)) e sp ofs).
    inv H6. right. apply is_reachable_intro with id b sz delta; auto. 
    exploit PERM; eauto. intros [A|A]; try contradiction.
    left. eapply Mem.perm_unchanged_on; eauto.
    red; intros.
      intros N. apply H6; clear H6.
      exploit me_inv; eauto. intros [id [lv B]].
      exploit BOUND0; eauto. intros C.
      apply is_reachable_intro with id b0 lv delta; auto; omega.
    eauto with mem. }
  eapply IntInc. assumption.
  intros. exploit (H2 b). xomega. unfold as_inj, join. rewrite H5.
            destruct (disjoint_extern_local _ WD2 b).
              assert (extern_of f1 = extern_of f2) by eapply IntInc. 
              rewrite H8, H7. 
              intros. apply eq_sym in H9. 
              apply (ME_INCR _ _ _ H9 H6). 
           rewrite H7 in H5; discriminate. 
  eapply IHstructured_match_callstack; eauto. 
    intros. eapply H0; eauto. xomega. 
    intros. eapply H2; eauto. xomega.
Qed.

Lemma structured_match_callstack_match_globalenvs: 
      forall mu m tm cs bound tbound
           (MCS: structured_match_callstack mu m tm cs bound tbound),
      exists hi, Ple hi bound /\ Ple hi tbound /\ 
                 match_globalenvs prog (restrict (as_inj mu) (vis mu)) hi.
Proof. intros mu m tm cs.
  induction cs; intros; inv MCS.
    exists hi; intuition.
  inv MENV.
  eapply IHcs.
  eapply structured_match_callstack_incr_bound; try eassumption.
  xomega. xomega.
Qed.

Lemma structured_match_callstack_ext: forall mu m1 m2 cs bound 
  tbound
  (MCS : structured_match_callstack mu m1 m2 cs bound tbound)
  m1' (FwdSrc : mem_forward m1 m1')
  nu vals1 vals2
  (Hnu: nu = replace_locals mu
                      (fun b0 : Values.block =>
                       locBlocksSrc mu b0 &&
                       REACH m1 (exportedSrc mu vals1) b0)
                      (fun b0 : Values.block =>
                       locBlocksTgt mu b0 &&
                       REACH m2 (exportedTgt mu vals2) b0))
  (SMvalMu : sm_valid mu m1 m2)
  (PG : meminj_preserves_globals (Genv.globalenv prog) (as_inj mu))
  nu' (INC : extern_incr nu nu')
  (GSep : globals_separate tge nu nu')
  (UNMAPPED : Mem.unchanged_on
                (fun (b : Values.block) (_ : Z) =>
                 locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1
                m1')
   m2' (FwdTgt : mem_forward m2 m2') (OUTOFREACH : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2')
 

  ret1 ret2 (WDnu' : SM_wd nu') (WDmu : SM_wd mu) (WDnu : SM_wd nu)
  (BND: Ple bound (Mem.nextblock m1))
  (TBND:Ple tbound (Mem.nextblock m2)),
structured_match_callstack
  (replace_externs nu'
        (fun b : Values.block =>
         DomSrc nu' b &&
         (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
        (fun b : Values.block =>
         DomTgt nu' b &&
         (negb (locBlocksTgt nu' b) && REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
   m1' m2' cs bound tbound.
Proof.
intros.
assert (VisMuNu':=replace_locals_extern_incr_vis _ _ _ _ Hnu _ INC WDnu' (ret1::nil) m1').  

assert (IncRestr: inject_incr (restrict (as_inj mu) (vis mu))
  (restrict (as_inj nu')
     (vis
        (replace_externs nu'
           (fun b : Values.block =>
            DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) &&
             REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
           (fun b : Values.block =>
            DomTgt nu' b &&
            (negb (locBlocksTgt nu' b) &&
             REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))))).
     subst.
        assert (IncAll := extern_incr_as_inj _ _ INC WDnu').
        rewrite replace_locals_as_inj in IncAll.
     intros b; intros.
     destruct (restrictD_Some _ _ _ _ _ H); clear H. 
     apply restrictI_Some.
       apply (IncAll _ _ _ H0).
     unfold vis. rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc.
     apply VisMuNu'. assumption.
generalize dependent tbound.
generalize dependent bound.
induction cs; intros bound HBound tbound MCS HTbound.
(* base case *)
  inv MCS.
  eapply st_mcs_nil with hi; eauto.
  rewrite replace_externs_as_inj.
  clear UNMAPPED OUTOFREACH.
  inv H. 
        assert (IncAll := extern_incr_as_inj _ _ INC WDnu').
        rewrite replace_locals_as_inj in IncAll.
        destruct INC as [EINC [LINC INC]]. 
        rewrite replace_locals_extern in EINC.
        rewrite replace_locals_local in LINC.
        rewrite replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
                replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
                replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
                replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt in INC.
        destruct INC as [INC_ES [INC_ET [INC_LS [INC_LT [INC_PS [INC_PT [INC_FS INC_FT]]]]]]].
  constructor; try eassumption. 
     intros. specialize (DOMAIN _ H H2). clear H2 IMAGE SYMBOLS FUNCTIONS VARINFOS.
     apply IncRestr. assumption.
     
  intros. 
        destruct (restrictD_Some _ _ _ _ _ H2); clear H2.
    case_eq (as_inj (restrict_sm mu (vis mu)) b1). 
    intros [b2' delta'] EQ.
      eapply (IMAGE b1 b2 delta); try eassumption.
        rewrite restrict_sm_all in EQ.
        destruct (restrictD_Some _ _ _ _ _ EQ).
        rewrite (IncAll _ _ _ H2) in H4. inv H4.  trivial.
    intros. rewrite restrict_sm_all in H2.
       red in GSep. 
       rewrite replace_locals_as_inj in GSep.
       destruct (restrictD_None' _ _ _ H2); clear H2.
         apply find_var_info_isGlobal in H.
         specialize (genvs_domain_eq_isGlobal _ _ GDE_lemma). unfold ge. 
         intros ZZ. rewrite ZZ in H.
         rewrite (GSep _ _ _ H6 H4) in H; discriminate. 
       destruct H6 as [bb2 [dd [AImu LF]]].
       specialize (IncAll _ _ _ AImu). 
       rewrite IncAll in H4. inv H4.
       apply meminj_preserves_genv2blocks in PG.
       destruct PG as [PGA [PGB PGC]].
       eapply PGC; try eassumption.
       unfold genv2blocks. simpl. exists gv; assumption.
(* inductive case *) 
  inv MCS.
  assert (IncAll := extern_incr_as_inj _ _ INC WDnu').
  red in GSep.
  destruct INC as [EINC [LINC INC]]. 
        rewrite replace_locals_extern in EINC.
        rewrite replace_locals_local in LINC.
        rewrite replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
                replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
                replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
                replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt in INC.
        destruct INC as [INC_ES [INC_ET [INC_LS [INC_LT [INC_PS [INC_PT [INC_FS INC_FT]]]]]]].
        rewrite replace_locals_as_inj in *.
  constructor.
    apply forward_nextblock in FwdSrc. xomega. 
    apply forward_nextblock in FwdTgt. xomega.
   (*match_temps*)
     clear IHcs.
     rewrite replace_externs_as_inj.
     eapply match_temps_invariant; try eassumption.
   (*match_env*)
     clear IHcs. 
     rewrite replace_externs_as_inj.
     inv MENV.
     constructor; trivial.
      intros. specialize (me_vars0 id).
        inv me_vars0; constructor.
        inv H1.
        econstructor; try eassumption.
        apply IncRestr. assumption.
    intros. 
    remember (restrict (as_inj mu) (vis mu) b) as d.
    destruct d; apply eq_sym in Heqd.
       destruct p.
       specialize (IncRestr _ _ _ Heqd). rewrite IncRestr in H.
       inv H. apply (me_inv0 _ _ Heqd). 
    destruct (restrictD_Some _ _ _ _ _ H); clear H. 
    rewrite INC_LT in SPlocal. apply as_inj_locTgt in H0; trivial.
    rewrite <- LINC in H0. 
    rewrite (incr_local_restrictvis _ WDmu _ _ _ H0) in Heqd; discriminate.     
  (*match_bounds*)
    eapply match_bounds_invariant; eauto. 
    intros. eapply FwdSrc; eauto. red.
    exploit me_bounded; eauto. xomega. 
  (* padding-freeable *)
  red; intros. 
  rewrite replace_externs_as_inj.
  destruct (is_reachable_from_env_dec (restrict (as_inj mu) (vis mu)) e sp ofs).
  inv H0. right. apply is_reachable_intro with id b sz delta; auto. 
  exploit PERM; eauto. intros [A|A]; try contradiction.
  left.
  eapply Mem.perm_unchanged_on; eauto.
    unfold local_out_of_reach.
      rewrite replace_locals_locBlocksTgt, replace_locals_local, replace_locals_pubBlocksSrc.
      intros. split. apply SPlocal. 
      intros.
      destruct (Mem.perm_dec m1 b0 (ofs - delta) Max Nonempty);
         try (left; assumption).
      right. destruct (local_DomRng _ WDmu _ _ _ H1).
      rewrite H2; simpl.
      exfalso. elim H0; clear H0.
      assert (RLoc: restrict (as_inj mu) (vis mu) b0 = Some (sp,delta)).
         apply restrictI_Some.
           apply joinI; right; split; try eassumption.
             destruct (disjoint_extern_local _ WDmu b0); congruence.
           unfold vis; simpl; rewrite H2; trivial.
      exploit me_inv; eauto.
         intros [id [lv B]]. exploit BOUND0; eauto. intros C.
      apply is_reachable_intro with id b0 lv delta; eauto. xomega.
    eauto with mem.
      rewrite replace_externs_locBlocksTgt. 
      rewrite <- INC_LT. apply SPlocal.
     
  rewrite replace_externs_local, <- LINC. assumption.
      
  (* induction *)
    eapply IHcs; try eassumption. 
      inv MENV. xomega.
      xomega.
Qed.

(*LENB: We omit the clauses INJ and PG, since they are required for the 
  enitre mu, not just restrict mu (vis mu), and hence better enforced 
  uniformly in definition MATCHCore below*)
Inductive structured_match_cores: core_data -> SM_Injection -> CSharpMin_core -> mem -> CMin_core -> mem -> Prop :=
  | SMC_states:
      forall d fn s k e le m tfn ts tk sp te tm cenv xenv mu lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (*(MINJ: Mem.inject (as_inj mu) m tm)*)
      (MCS: structured_match_callstack mu m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk  cenv xenv cs)
      (*(PG: meminj_preserves_globals ge (as_inj mu))*),
      structured_match_cores d mu (CSharpMin_State fn s k e le) m
                   (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm
  | SMC_state_seq:
      forall d fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv mu lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (*(MINJ: Mem.inject (as_inj mu) m tm)*)
      (MCS: structured_match_callstack mu m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs)
      (*(PG: meminj_preserves_globals ge (as_inj mu))*),
      structured_match_cores d mu (CSharpMin_State fn (Csharpminor.Sseq s1 s2) k e le) m
                   (CMin_State tfn ts1 tk (Vptr sp Int.zero) te) tm
  | SMC_callstate:
      forall d fd args k m tfd targs tk tm mu cs cenv
      (TR: transl_fundef fd = OK tfd)
      (*(MINJ: Mem.inject (as_inj mu) m tm)*)
      (MCS: structured_match_callstack mu m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: val_list_inject (restrict (as_inj mu) (vis mu)) args targs)
      (*(PG: meminj_preserves_globals ge (as_inj mu))*),
 
      structured_match_cores d mu (CSharpMin_Callstate fd args k) m
                   (CMin_Callstate tfd targs tk) tm
  | SMC_returnstate:
      forall d v k m tv tk tm mu cs cenv
      (*(MINJ: Mem.inject (as_inj mu) m tm)*)
      (MCS: structured_match_callstack mu m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: val_inject (restrict (as_inj mu) (vis mu)) v tv)
      (*(PG: meminj_preserves_globals ge (as_inj mu))*),
      structured_match_cores d mu (CSharpMin_Returnstate v k) m
                   (CMin_Returnstate tv tk) tm.

Definition MATCH d mu c1 m1 c2 m2:Prop :=
  structured_match_cores d mu c1 m1 c2 m2 (*(restrict_sm mu (vis mu)) doesn't work here, since 
                              some of the conditions of match_env are "global"*) /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\
  Mem.inject (as_inj mu) m1 m2(* /\ protected m1 mu*).

Lemma MATCH_sm_wd: forall d mu c1 m1 c2 m2, 
          MATCH d mu c1 m1 c2 m2 -> 
          SM_wd mu.
Proof. intros. apply H. Qed.

Lemma MATCH_genv: forall d mu c1 m1 c2 m2
                  (MC:MATCH d mu c1 m1 c2 m2),
          meminj_preserves_globals ge (extern_of mu) /\
          (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (WD:= MATCH_sm_wd _ _ _ _ _ _ MC).
  assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC.
Qed.

Lemma MATCH_visible: forall d mu c1 m1 c2 m2, 
          MATCH d mu c1 m1 c2 m2 -> 
          REACH_closed m1 (vis mu).
Proof. intros. apply H. Qed.

Lemma structured_match_callstack_restrict: forall mu m1 m2 X
      (HX: forall b, vis mu b = true -> X b = true)
      (RC: REACH_closed m1 X) cs bound tbound
      (MCS: structured_match_callstack mu m1 m2 cs bound tbound),
      structured_match_callstack (restrict_sm mu X) m1 m2 cs  bound tbound.
Proof. intros until cs.
  induction cs; simpl; intros.
  inv MCS.
   econstructor; try eassumption.
   rewrite vis_restrict_sm.
   rewrite restrict_sm_all.
   rewrite restrict_nest; intuition.
  inv MCS. specialize (IHcs _ _ MCS0).
  econstructor; try eassumption.
   rewrite vis_restrict_sm.
   rewrite restrict_sm_all.
   rewrite restrict_nest; intuition.

   rewrite vis_restrict_sm.
   rewrite restrict_sm_all.
   rewrite restrict_nest; intuition.

   rewrite vis_restrict_sm.
   rewrite restrict_sm_all.
   rewrite restrict_nest; intuition.

   rewrite restrict_sm_locBlocksTgt. assumption.

   intros. 
   rewrite restrict_sm_local in H.
   destruct (restrictD_Some _ _ _ _ _ H).
   apply (ME_INCR _ _ _ H1 H0).
Qed.

Lemma structured_match_cores_restrict: forall mu d m1 m2 c1 c2 X
      (HX: forall b, vis mu b = true -> X b = true)
      (RC: REACH_closed m1 X) 
      (MC: structured_match_cores d mu c1 m1 c2 m2),
 structured_match_cores d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  inv MC.
  eapply SMC_states; try eassumption.
   eapply structured_match_callstack_restrict; eassumption.
  eapply SMC_state_seq; try eassumption.
   eapply structured_match_callstack_restrict; eassumption.
  eapply SMC_callstate; try eassumption.
   eapply structured_match_callstack_restrict; eassumption.
   rewrite vis_restrict_sm. rewrite restrict_sm_all.
   rewrite restrict_nest; assumption.
  eapply SMC_returnstate; try eassumption.
   eapply structured_match_callstack_restrict; eassumption.
   rewrite vis_restrict_sm. rewrite restrict_sm_all.
   rewrite restrict_nest; assumption.
Qed.

Lemma MATCH_restrict: forall d mu c1 m1 c2 m2 X
          (MC: MATCH d mu c1 m1 c2 m2)
          (HX: forall b, vis mu b = true -> X b = true)
          (RC: REACH_closed m1 X),
          MATCH d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MC [RCLocs [PG [Glob [SMV [WD INJ]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  eapply structured_match_cores_restrict; eassumption.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RCLocs.
split. clear -PG HX Glob.
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition. 
split. 
  rewrite restrict_sm_frgnBlocksSrc. apply Glob.
split. 
  destruct SMV.
  split; intros.
    rewrite restrict_sm_DOM in H1.
    apply (H _ H1).
  rewrite restrict_sm_RNG in H1.
    apply (H0 _ H1).
split. assumption.
rewrite restrict_sm_all.
  eapply inject_restrict; eassumption.
(*apply protected_restr; trivial.*)
Qed.

Lemma MATCH_validblocks: 
forall d mu c1 m1 c2 m2, MATCH d mu c1 m1 c2 m2 -> 
        sm_valid mu m1 m2.
Proof. intros. apply H. Qed.

(*TODO: move*)
Lemma genv_next_symbol_exists' b (ge0 : Genv.t Csharpminor.fundef unit) l :
  list_norepet (map fst l) -> 
  (Plt b (Genv.genv_next ge0) ->
    exists id, ~List.In id (map fst l) /\ Genv.find_symbol ge0 id = Some b) -> 
  Plt b (Genv.genv_next (Genv.add_globals ge0 l)) ->
  exists id, Genv.find_symbol (Genv.add_globals ge0 l) id = Some b.
Proof.
revert ge0 b.
induction l; simpl; auto.
intros ge0 b ? ? H2.
destruct (H0 H2) as [? [? ?]].
solve[eexists; eauto].
intros ge0 b H H2 H3.
inv H.
destruct a; simpl in *.
eapply IHl; eauto.
intros Hplt.
destruct (ident_eq b (Genv.genv_next ge0)). 
* subst b.
exists i.
unfold Genv.add_global, Genv.find_symbol; simpl.
rewrite PTree.gss; auto.
* unfold Genv.add_global, Genv.find_symbol; simpl.
destruct H2 as [x H2].
unfold Genv.add_global in Hplt; simpl in Hplt; xomega.
exists x.
destruct H2 as [A B].
split; auto.
rewrite PTree.gso; auto.
Qed.

Lemma genv_next_symbol_exists b :
  list_norepet (map fst (prog_defs prog)) -> 
  Plt b (Genv.genv_next ge) -> 
  exists id, Genv.find_symbol ge id = Some b.
Proof.
intros Hnorepet H.
exploit genv_next_symbol_exists'; eauto.
simpl; xomega.
Qed.

Lemma genv_next_symbol_exists2 b :
  list_norepet (map fst (prog_defs prog)) -> 
  Psucc b = Genv.genv_next ge -> 
  exists id, Genv.find_symbol ge id = Some b.
Proof.
intros Hnorepet H.
apply genv_next_symbol_exists; auto.
xomega.
Qed.

Lemma match_globalenvs_init2:
  forall (R: list_norepet (map fst (prog_defs prog))) j,
  meminj_preserves_globals ge j ->
  match_globalenvs prog j (Genv.genv_next ge).
Proof.
  intros.
  destruct H as [A [B C]].
  constructor.
  * intros b D. 
  cut (exists id, Genv.find_symbol (Genv.globalenv prog) id = Some b).
  intros [id ID].
  eauto.
  exploit genv_next_symbol_exists; eauto.
  * intros. symmetry. eapply C; eauto.
  * intros. eapply Genv.genv_symb_range; eauto.
  * intros. eapply Genv.genv_funs_range; eauto.
  * intros. eapply Genv.genv_vars_range; eauto.
Qed.

Lemma Match_init_core: forall v 
  (vals1 : list val) (c1 : CSharpMin_core) (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (CSM_Ini :initial_core (csharpmin_eff_sem hf) ge v vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (R : list_norepet (map fst (prog_defs prog)))
  (J: forall b1 b2 d, j b1 = Some (b2, d) -> 
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (GFI: globalfunction_ptr_inject ge j)
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b),
exists c2 : CMin_core,
  initial_core (cmin_eff_sem hf) tge v vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2. 
Proof. 
  intros.
  unfold  CSharpMin_initial_core in CSM_Ini. unfold ge in *. unfold tge in *.
  destruct v; inv CSM_Ini.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H0. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz.
    apply eq_sym in Heqzz.
  2: discriminate.
  destruct f; try discriminate.
  case_eq (val_casted.val_has_type_list_func vals1 (sig_args (Csharpminor.funsig (Internal f)))).
  2: solve[intros cast; rewrite cast in H1; inv H1].
  intros cast. case_eq (val_casted.vals_defined vals1).
  2: solve[intros def; rewrite cast, def in H1; inv H1].
  intros def; rewrite cast,def in H1.

  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0 => 0
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0 => 0
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  intros l _.
  2: solve[inversion 2].

  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exists (CMin_Callstate tf vals2 Cminor.Kstop).
  split.
  simpl. 
  subst. inv Heqzz. inv FIND. rewrite H2.
  unfold CMin_initial_core. 
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.

  assert (Zlength vals2 = Zlength vals1) as ->. 
  { apply forall_inject_val_list_inject in VInj. clear - VInj. 
    induction VInj; auto. rewrite !Zlength_cons, IHVInj; auto. }

  assert (val_casted.val_has_type_list_func vals2
           (sig_args (funsig tf))=true) as ->.
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    assert (sig_args (funsig tf)
          = sig_args (Csharpminor.funsig (Internal f))) as ->.
    { erewrite sig_preserved; eauto. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (Csharpminor.funsig (Internal f)))); auto. }

  assert (val_casted.vals_defined vals2=true) as ->.
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto. }

  monadInv TR. rename x into tf.
  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0 => 0
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0 => 0
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned); simpl; auto. 
  intros l'. clear - l l'. elimtype False. omega.

  intros CONTRA.
  solve[elimtype False; auto].
  split.
    inv H1.
    eapply SMC_callstate with (cenv:=PTree.empty _)(cs := @nil frame); eauto.
    apply st_mcs_nil with (Genv.genv_next ge).
    eapply match_globalenvs_init2; auto.
      eapply restrict_preserves_globals. rewrite initial_SM_as_inj. assumption.
    unfold vis, initial_SM; simpl.
    intros b0 isGlob. apply REACH_nil. intuition.

  { destruct PG as [XX [Y Z]].
    unfold Ple. rewrite <-Pos.leb_le.
    destruct (Pos.leb (Genv.genv_next ge) (Mem.nextblock m1)) eqn:?; auto.
    rewrite Pos.leb_nle in Heqb0.
    assert (Heqb': (Genv.genv_next ge > Mem.nextblock m1)%positive) by xomega.
    assert (exists b0, Psucc b0 = Genv.genv_next ge).
    { destruct (Genv.genv_next ge). 
      exists ((b0~1)-1)%positive. simpl. auto.
      exists (Pos.pred (b0~0))%positive. rewrite Pos.succ_pred. auto. xomega.
      xomega. }
    destruct H as [b0 H].
    generalize H as H'; intro.
    apply genv_next_symbol_exists2 in H.
    destruct H as [id H].
    apply XX in H.
    apply J in H.
    destruct H as [H H3].
    specialize (HDomS _ H).
    unfold Mem.valid_block in HDomS. clear - Heqb' HDomS H'. xomega.
    auto. }

  { destruct PG as [XX [Y Z]].
    unfold Ple. rewrite <-Pos.leb_le.
    destruct (Pos.leb (Genv.genv_next ge) (Mem.nextblock m2)) eqn:?; auto.
    rewrite Pos.leb_nle in Heqb0.
    assert (Heqb': (Genv.genv_next ge > Mem.nextblock m2)%positive) by xomega.
    assert (exists b0, Psucc b0 = Genv.genv_next ge).
    { destruct (Genv.genv_next ge). 
      exists ((b0~1)-1)%positive. simpl. auto.
      exists (Pos.pred (b0~0))%positive. rewrite Pos.succ_pred. auto. xomega.
      xomega. }
    destruct H as [b0 H].
    generalize H as H'; intro.
    apply genv_next_symbol_exists2 in H.
    destruct H as [id H].
    apply XX in H.
    apply J in H.
    destruct H as [H H3].
    specialize (HDomT _ H3).
    unfold Mem.valid_block in HDomT. clear - Heqb' HDomT H'. xomega.
    auto. }

  constructor; auto. simpl; auto.
  apply forall_inject_val_list_inject.
  eapply restrict_forall_vals_inject; try eassumption.
  intuition. rewrite initial_SM_as_inj. assumption.
  intros b0 Hget. unfold vis. simpl. apply REACH_nil. intuition.
  simpl. 
  
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
    VInj J RCH PG GDE_lemma HDomS HDomT _ (eq_refl _))
   as [AA [BB [CC [DD [EE [FF GG]]]]]].
  intuition.
  rewrite initial_SM_as_inj. assumption.
  rewrite initial_SM_as_inj. assumption.
Qed.

Lemma MATCH_AfterExternal: 
forall mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
  (MemInjMu : Mem.inject (as_inj mu) m1 m2)
  (MatchMu : MATCH st1 mu st1 m1 st2 m2)
  (AtExtSrc : at_external (csharpmin_eff_sem hf) st1 = Some (e, ef_sig, vals1))
  (AtExtTgt : at_external (cmin_eff_sem hf) st2 = Some (e', ef_sig', vals2))
  (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
  (pubSrc' : Values.block -> bool)
  (pubSrcHyp : pubSrc' =
              (fun b : Values.block =>
               locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
  (pubTgt' : Values.block -> bool)
  (pubTgtHyp : pubTgt' =
              (fun b : Values.block =>
               locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
  nu
  (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
  nu' ret1 m1' ret2 m2' 
  (INC : extern_incr nu nu')
  (SEP : globals_separate tge nu nu')
  (WDnu' : SM_wd nu')
  (SMvalNu' : sm_valid nu' m1' m2')
  (MemInjNu' : Mem.inject (as_inj nu') m1' m2')
  (RValInjNu' : val_inject (as_inj nu') ret1 ret2)
  (FwdSrc : mem_forward m1 m1')
  (FwdTgt : mem_forward m2 m2')
  (frgnSrc' : Values.block -> bool)
  (frgnSrcHyp : frgnSrc' =
               (fun b : Values.block =>
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) &&
                REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
  (frgnTgt' : Values.block -> bool)
  (frgnTgtHyp : frgnTgt' =
               (fun b : Values.block =>
                DomTgt nu' b &&
                (negb (locBlocksTgt nu' b) &&
                 REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
  mu' 
  (Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
  (UnchPrivSrc : Mem.unchanged_on
                (fun (b : Values.block) (_ : Z) =>
                 locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1
                m1')
  (UnchLOOR : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists (st1' : CSharpMin_core) (st2' : CMin_core),
  after_external (csharpmin_eff_sem hf) (Some ret1) st1 = Some st1' /\
  after_external (cmin_eff_sem hf) (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros. 
 destruct MatchMu as [MC [RC [PG [GF [VAL [WDmu INJ]]]]]].
 (*assert (PGR: meminj_preserves_globals (Genv.globalenv prog)
                  (restrict (as_inj mu) (vis mu))).
      eapply restrict_preserves_globals; try eassumption.
        unfold vis; intuition.*)
 inv MC; simpl in *; inv AtExtSrc.
  destruct fd; inv H0.
  destruct tfd; inv AtExtTgt.
  inv TR.
  destruct (observableEF_dec hf e1); inv H0; inv H1.
  exists (CSharpMin_Returnstate ret1 k). eexists.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
assert (INCvisNu': inject_incr
  (restrict (as_inj nu')
     (vis
        (replace_externs nu'
           (fun b : Values.block =>
            DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) &&
             REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
           (fun b : Values.block =>
            DomTgt nu' b &&
            (negb (locBlocksTgt nu' b) &&
             REACH m2' (exportedTgt nu' (ret2 :: nil)) b))))) (as_inj nu')).
      unfold vis. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
      apply restrict_incr. 
assert (RC': REACH_closed m1' (mapped (as_inj nu'))).
        eapply inject_REACH_closed; eassumption.
assert (PGnu': meminj_preserves_globals (Genv.globalenv prog) (as_inj nu')). 
  eapply meminj_preserves_globals_extern_incr_separate. eassumption.
    rewrite replace_locals_as_inj. assumption.
    assumption. 
    specialize (genvs_domain_eq_isGlobal _ _ GDE_lemma). intros GL.
    red. unfold ge in GL. rewrite GL. apply SEP.
assert (RR1: REACH_closed m1'
  (fun b : Values.block =>
   locBlocksSrc nu' b
   || DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
     assumption.
  specialize (IHL _ H1); clear H1.
  apply orb_true_iff in IHL.
  remember (locBlocksSrc nu' b') as l.
  destruct l; apply eq_sym in Heql.
  (*case locBlocksSrc nu' b' = true*)
    clear IHL.
    remember (pubBlocksSrc nu' b') as p.
    destruct p; apply eq_sym in Heqp.
      assert (Rb': REACH m1' (mapped (as_inj nu')) b' = true).
        apply REACH_nil. 
        destruct (pubSrc _ WDnu' _ Heqp) as [bb2 [dd1 [PUB PT]]].
        eapply mappedI_true.
         apply (pub_in_all _ WDnu' _ _ _ PUB).
      assert (Rb:  REACH m1' (mapped (as_inj nu')) b = true).
        eapply REACH_cons; try eassumption.
      specialize (RC' _ Rb).
      destruct (mappedD_true _ _ RC') as [[b2 d1] AI'].
      remember (locBlocksSrc nu' b) as d.
      destruct d; simpl; trivial.
      apply andb_true_iff. 
      split. eapply as_inj_DomRng; try eassumption.
      eapply REACH_cons; try eassumption.
        apply REACH_nil. unfold exportedSrc.
        rewrite (pubSrc_shared _ WDnu' _ Heqp). intuition.
      destruct (UnchPrivSrc) as [UP UV]; clear UnchLOOR.
        specialize (UP b' z Cur Readable). 
        specialize (UV b' z). 
        destruct INC as [_ [_ [_ [_ [LCnu' [_ [PBnu' [_ [FRGnu' _]]]]]]]]].
        rewrite <- LCnu'. rewrite replace_locals_locBlocksSrc.  
        rewrite <- LCnu' in Heql. rewrite replace_locals_locBlocksSrc in *.
        rewrite <- PBnu' in Heqp. rewrite replace_locals_pubBlocksSrc in *.
        clear INCvisNu'. 
        rewrite Heql in *. simpl in *. intuition.
        assert (VB: Mem.valid_block m1 b').
          eapply VAL. unfold DOM, DomSrc. rewrite Heql. intuition.
        apply (H VB) in H2.
        rewrite (H0 H2) in H4. clear H H0.
        remember (locBlocksSrc mu b) as q.
        destruct q; simpl; trivial; apply eq_sym in Heqq.
        assert (Rb : REACH m1 (vis mu) b = true).
           eapply REACH_cons; try eassumption.
           apply REACH_nil. unfold vis. rewrite Heql; trivial.
        specialize (RC _ Rb). unfold vis in RC.
           rewrite Heqq in RC; simpl in *.
        rewrite replace_locals_frgnBlocksSrc in FRGnu'.
        rewrite FRGnu' in RC.
        apply andb_true_iff.  
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ RC). intuition.
        apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ RC). intuition.
  (*case DomSrc nu' b' &&
    (negb (locBlocksSrc nu' b') &&
     REACH m1' (exportedSrc nu' (ret1 :: nil)) b') = true*)
    destruct IHL. inv H.
    apply andb_true_iff in H. simpl in H. 
    destruct H as[DomNu' Rb']. 
    clear INC SEP INCvisNu' UnchLOOR UnchPrivSrc.
    remember (locBlocksSrc nu' b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    apply andb_true_iff.
    split. assert (RET: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
              constructor. assumption. constructor.
           destruct (REACH_as_inj _ WDnu' _ _ _ _ MemInjNu' RET
               _ Rb' (fun b => true)) as [b2 [d1 [AI' _]]]; trivial.
           assert (REACH m1' (mapped (as_inj nu')) b = true).
             eapply REACH_cons; try eassumption.
             apply REACH_nil. eapply mappedI_true; eassumption.
           specialize (RC' _ H). 
           destruct (mappedD_true _ _ RC') as [[? ?] ?].
           eapply as_inj_DomRng; eassumption.
    eapply REACH_cons; try eassumption.
    
assert (RRC: REACH_closed m1' (fun b : Values.block =>
                         mapped (as_inj nu') b &&
                           (locBlocksSrc nu' b
                            || DomSrc nu' b &&
                               (negb (locBlocksSrc nu' b) &&
                           REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))).
  eapply REACH_closed_intersection; eassumption.
assert (GFnu': forall b, isGlobalBlock (Genv.globalenv prog) b = true ->
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
     intros. specialize (GF _ H).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in GF.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ GF). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ GF). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ GF). intuition.
split.
  unfold vis in *.
  rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
  econstructor; try eassumption.
    eapply structured_match_callstack_incr_bound.
      eapply structured_match_callstack_ext with
       (mu:=mu)(nu':=nu'); try reflexivity; try eassumption.
       eapply eff_after_check1 with (mu:=mu); try eassumption; try reflexivity.
         eapply forall_vals_inject_restrictD; eassumption.
       apply (forward_nextblock _ _ FwdSrc).
       apply (forward_nextblock _ _ FwdTgt).
    rewrite (*restrict_sm_all, *)replace_externs_as_inj.
      eapply restrict_val_inject; try eassumption.
       intros.
        destruct (getBlocks_inject (as_inj nu') (ret1::nil) (ret2::nil))
           with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
          constructor. assumption. constructor.
         unfold vis. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
        remember (locBlocksSrc nu' b) as d.
        destruct d; simpl; trivial. apply andb_true_iff.
        split. eapply as_inj_DomRng; eassumption.
        apply REACH_nil. unfold exportedSrc.
           rewrite H. trivial.
unfold vis.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
intuition.
Qed.

Lemma MATCH_safely_halted: forall cd mu c1 m1 c2 m2 v1
     (SMC: structured_match_cores cd mu c1 m1 c2 m2)
     (HALT: halted (CSharpMin_core_sem hf) c1 = Some v1),
exists v2, halted (CMin_core_sem hf) c2 = Some v2 /\ 
           val_inject (restrict (as_inj mu) (vis mu)) v1 v2.
Proof.
  intros.
  inv SMC; simpl in *; inv HALT.
  destruct k; inv H0. exists tv.
  inv MK. split; trivial.
Qed.

Lemma MATCH_at_external: forall mu st1 m1 st2 m2 e vals1 sig
     (MC: structured_match_cores st1 mu st1 m1 st2 m2) 
     (AtExt: at_external (CSharpMin_core_sem hf) st1 = Some (e, sig, vals1)),
  exists vals2, Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
                at_external (CMin_core_sem hf) st2 = Some (e, sig, vals2).
Proof.
  intros. 
  inv MC; simpl in *; inv AtExt.
  destruct fd; inv H0.
  inv TR.
  destruct (observableEF_dec hf e0); inv H1.
  exists targs.
  split; trivial. apply val_list_inject_forall_inject; eassumption. 
Qed.

Lemma structured_match_callstack_replace_locals mu m1 m2 pubSrc' pubTgt': forall cs bound tbound
        (MCS : structured_match_callstack mu m1 m2 cs bound tbound),
      structured_match_callstack (replace_locals mu pubSrc' pubTgt') m1 m2 cs bound tbound.
Proof. intros cs; induction cs; intros.
  inv MCS; econstructor; 
      try rewrite replace_locals_as_inj;
      try rewrite replace_locals_vis; eauto.
  inv MCS; econstructor; 
      try rewrite replace_locals_local;
      try rewrite replace_locals_as_inj;
      try rewrite replace_locals_vis; 
      try rewrite replace_locals_locBlocksTgt; eauto. 
Qed. 

Lemma MATCH_atExternal: forall mu c1 m1 c2 m2 e vals1 ef_sig
       (MTCH: MATCH c1 mu c1 m1 c2 m2)
       (AtExtSrc: at_external (csharpmin_eff_sem hf) c1 = Some (e, ef_sig, vals1)),
     Mem.inject (as_inj mu) m1 m2 /\
     exists vals2,
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
       at_external (cmin_eff_sem hf) c2 = Some (e, ef_sig, vals2) /\
      (forall pubSrc' pubTgt',
       pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
       pubTgt' = (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
       forall nu : SM_Injection, nu = replace_locals mu pubSrc' pubTgt' ->
       MATCH c1 nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2).
Proof. intros. destruct MTCH as [MC [RC [PG [GF [SMV [WD INJ]]]]]].
destruct (MATCH_at_external _ _ _ _ _ _ _ _ MC AtExtSrc) as [vals2 [ValsInj AtExtTgt]]. 
split; trivial.
exists vals2. split; trivial. split; trivial.
exploit replace_locals_wd_AtExternal; try eassumption.
  apply forall_vals_inject_restrictD in ValsInj. eassumption.
intros WDnu.
intros.
assert (SMVnu: sm_valid nu m1 m2).
  red. subst nu. rewrite replace_locals_DOM, replace_locals_RNG. apply SMV.
  split. (*MATCH*)
    split. inv MC; inv AtExtSrc.
      econstructor; try eassumption. 
        eapply structured_match_callstack_replace_locals; eauto.
        rewrite replace_locals_as_inj, replace_locals_vis. trivial.    
    subst nu.
      rewrite replace_locals_vis, replace_locals_as_inj, replace_locals_frgnBlocksSrc.
      intuition. subst; assumption.
    eapply inject_shared_replace_locals; try eassumption.
      subst; trivial.
Qed.

Lemma match_callstack_freelist:
  forall mu cenv tf e le te sp lo hi cs m m' tm (WD: SM_wd mu),
  Mem.inject (as_inj mu) m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  structured_match_callstack mu m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  exists tm',
  Mem.free tm sp 0 tf.(fn_stackspace) = Some tm'
  /\ structured_match_callstack mu m' tm' cs (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject (as_inj mu) m' tm'.
Proof.
  intros until tm; intros WDmu INJ FREELIST MCS. inv MCS. inv MENV.
  assert ({tm' | Mem.free tm sp 0 (fn_stackspace tf) = Some tm'}).
  apply Mem.range_perm_free.
  red; intros.
  exploit PERM; eauto. intros [A | A].
  auto.
  inv A. assert (Mem.range_perm m b 0 sz Cur Freeable). 
  eapply free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
  replace ofs with ((ofs - delta) + delta) by omega. 
  destruct (restrictD_Some _ _ _ _ _ H1); clear H1.
  eapply Mem.perm_inject; eauto. apply H3. omega. 
  destruct X as  [tm' FREE].
  exploit nextblock_freelist; eauto. intro NEXT.
  exploit Mem.nextblock_free; eauto. intro NEXT'.
  exists tm'. split. auto. split.
  rewrite NEXT; rewrite NEXT'.
  apply structured_match_callstack_incr_bound with lo sp; try omega.
  apply structured_match_callstack_intern_invariant with mu m tm; auto.
     apply intern_incr_refl.
  intros. eapply perm_freelist; eauto.
  intros. eapply Mem.perm_free_1; eauto. xomega. xomega.
  eapply Mem.free_inject; eauto.
  intros. exploit me_inv0; eauto.
    apply restrictI_Some; try eassumption.
    destruct (joinD_Some _ _ _ _ _ H) as [EXT | [_ LOC]]; clear H.
      destruct (extern_DomRng _ WDmu _ _ _ EXT).
      rewrite (extBlocksTgt_locBlocksTgt _ WDmu _ H2) in SPlocal.
      discriminate.
    unfold vis. destruct (local_DomRng _ WDmu _ _ _ LOC).
      intuition.
  intros [id [sz A]]. 
  exists 0; exists sz; split.
  eapply in_blocks_of_env; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_max. eauto. 
Qed.

Lemma var_addr_correct:
  forall cenv id mu tf e le te sp lo hi m cs tm b,
  structured_match_callstack mu m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  eval_var_addr ge e id b ->
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm (var_addr cenv id) tv
  /\ val_inject (restrict (as_inj mu) (vis mu)) (Vptr b Int.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var (restrict (as_inj mu) (vis mu)) sp e!id cenv!id).
    inv H. inv MENV. auto.
  inv H1. inv H0; rewrite H1 in H2; inv H2.
  (* local *)
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  assumption.
  (* global *)
  exploit structured_match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  inv H0. rewrite H5 in H3. inv H3.
  destruct H2. inv H2. (*   inv H.*)
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct; eauto. 
    rewrite (symbols_preserved prog); assumption.
  econstructor; eauto.
Qed.

Lemma transl_expr_correct:
  forall mu m tm cenv tf e lenv te sp lo hi cs
    (MINJ: Mem.inject (as_inj mu) m tm)
    (RC: REACH_closed m (vis mu))
    (MTCH: structured_match_callstack mu m tm
             (Frame cenv tf e lenv te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_expr ge e lenv m a v ->
  forall ta app
    (TR: transl_expr cenv a = OK (ta, app)),
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm ta tv
  /\ val_inject (restrict (as_inj mu) (vis mu)) v tv
  /\ val_match_approx app v.
Proof.
  induction 4; intros; simpl in TR; try (monadInv TR).
  (* Etempvar *)
  inv MTCH. exploit MTMP; eauto. intros [tv [A B]]. 
  exists tv; split. constructor; auto. split.
    inv B; econstructor; try eassumption. trivial.
    exact I.
  (* Eaddrof *)
  exploit var_addr_correct; eauto. intros [tv [A B]].
  exists tv; split. trivial.
    split; trivial. red. auto. 
  (* Econst *)
  exploit transl_constant_correct; eauto. 
  destruct (transl_constant cst) as [tcst a]; inv TR.
  intros [tv [A [B C]]].
  exists tv; split. constructor; eauto. eauto.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 [INJ1 APP1]]].
  unfold Csharpminor.eval_unop in H0. 
  destruct (Approx.unop_is_redundant op x0) eqn:?; inv EQ0.
  (* -- eliminated *)
  exploit approx_unop_is_redundant_sound; eauto. intros. 
  replace v with v1 by congruence.
  exists tv1; auto.
  (* -- preserved *)
  exploit make_unop_correct; eauto. intros [tv [A B]].
  exists tv; split. auto. split. auto. eapply approx_of_unop_sound; eauto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 [INJ1 APP1]]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 [INJ2 APP2]]].
  exploit eval_binop_compat; eauto.
    eapply inject_restrict; eassumption.
  intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. split. auto. eapply approx_of_binop_sound; eauto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 [INJ1 APP1]]].
  exploit Mem.loadv_inject; eauto.
     eapply val_inject_restrictD; apply INJ1.
  intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto.
  destruct v1; simpl in H0; try discriminate.
  split.
  inv INJ; try econstructor; try reflexivity.    
    eapply restrictI_Some; try eassumption.
    clear LOAD.
    apply RC.
    clear - H0 INJ1. 
    inv INJ1.
    destruct (restrictD_Some _ _ _ _ _ H2); clear H2.
       eapply REACH_load_vis; eassumption.
    eapply approx_of_chunk_sound; apply H0. 
Qed.

Lemma transl_exprlist_correct:
  forall mu m tm cenv tf e lenv te sp lo hi cs
    (MINJ: Mem.inject (as_inj mu) m tm)
    (RC: REACH_closed m (vis mu))
    (MATCH: structured_match_callstack mu m tm
             (Frame cenv tf e lenv te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_exprlist ge e lenv m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge (Vptr sp Int.zero) te tm ta tv
  /\ val_list_inject (restrict (as_inj mu) (vis mu)) v tv.
Proof.
  induction 4; intros; monadInv TR.
  exists (@nil val); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 [VINJ1 APP1]]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.

Lemma match_env_alloc:
  forall mu1 id cenv e sp lo m1 sz m2 b ofs mu2 (WD2: SM_wd mu2),
  match_env (as_inj mu1) (PTree.remove id cenv) e sp lo (Mem.nextblock m1) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  intern_incr mu1 mu2 ->
  as_inj mu2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> as_inj mu2 b' = as_inj mu1 b') ->
  e!id = None ->
  match_env (as_inj mu2) cenv (PTree.set id (b, sz) e) sp lo (Mem.nextblock m2).
Proof.
  intros until mu2; intros WD2 ME ALLOC CENV INCR SAME OTHER ENV.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  inv ME; constructor.
(* vars *)
  intros. rewrite PTree.gsspec. destruct (peq id0 id).
  (* the new var *)
  subst id0. rewrite CENV. constructor. econstructor. eauto. 
  rewrite Int.add_commut; rewrite Int.add_zero; auto.
  (* old vars *)
  generalize (me_vars0 id0). rewrite PTree.gro; auto. intros M; inv M.
  constructor.
    inv H1. apply (intern_incr_as_inj _ _ INCR) in H5; trivial.
            econstructor; eassumption.
  constructor. 
(* low-high *)
  rewrite NEXTBLOCK; xomega.
(* bounded *)
  intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inv H. rewrite NEXTBLOCK; xomega.
  exploit me_bounded0; eauto. rewrite NEXTBLOCK; xomega.
(* inv *)
  intros. destruct (eq_block b (Mem.nextblock m1)).
  subst b. rewrite SAME in H; inv H. exists id; exists sz. apply PTree.gss. 
  rewrite OTHER in H; auto. exploit me_inv0; eauto. 
  intros [id1 [sz1 EQ]]. exists id1; exists sz1. rewrite PTree.gso; auto. 
    intros N. subst id1. rewrite EQ in ENV. discriminate.
Qed.

Lemma structured_match_callstack_set_temp:
  forall mu cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
  val_inject (restrict (as_inj mu) (vis mu)) v tv ->
  structured_match_callstack mu m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  structured_match_callstack mu m tm (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H0. constructor; auto.
  eapply match_temps_assign; eauto. 
Qed.

Lemma structured_match_callstack_alloc_left:
  forall mu1 m1 tm id cenv tf e lenv te sp lo cs sz m2 b mu2 ofs
        (WD1: SM_wd mu1) (WD2: SM_wd mu2),
  structured_match_callstack mu1 m1 tm
    (Frame (PTree.remove id cenv) tf e lenv te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  intern_incr mu1 mu2 ->
  as_inj mu2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> as_inj mu2 b' = as_inj mu1 b') ->
  e!id = None ->
  structured_match_callstack mu2 m2 tm
    (Frame cenv tf (PTree.set id (b, sz) e) lenv te sp lo (Mem.nextblock m2) :: cs)
    (Mem.nextblock m2) (Mem.nextblock tm).
Proof.
  intros. inv H. 
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  assert (LO: Ple lo (Mem.nextblock m1)) by (eapply me_low_high; eauto). 
  constructor.
  xomega.
  auto.
  eapply match_temps_invariant; try eassumption.
     eapply intern_incr_restrict; eassumption.
  rewrite <- restrict_sm_all. rewrite <- restrict_sm_all in MENV.
    eapply match_env_alloc; try eassumption.
      eapply restrict_sm_WD; try eassumption. intuition.
      eapply restrict_sm_intern_incr; eassumption.
      rewrite restrict_sm_all. eapply restrictI_Some; try eassumption.
       destruct (joinD_Some _ _ _ _ _ H3) as [EXT | [EXT LOC]].
         destruct (extern_DomRng _ WD2 _ _ _ EXT).
         assert (L: extBlocksTgt mu1 = extBlocksTgt mu2) by eapply H2.
         rewrite <- L in H6.
         apply (extBlocksTgt_locBlocksTgt _ WD1) in H6. 
         rewrite H6 in SPlocal. discriminate.
       unfold vis. destruct (local_DomRng _ WD2 _ _ _ LOC).
         rewrite H. reflexivity.
    intros. specialize (H4 _ H). repeat rewrite restrict_sm_all.
      remember (restrict (as_inj mu2) (vis mu2) b') as d.
      destruct d; apply eq_sym in Heqd.
        destruct p. destruct (restrictD_Some _ _ _ _ _ Heqd); clear Heqd.
        rewrite H4 in H6. apply eq_sym.
        apply restrictI_Some; try eassumption.
          eapply (intern_incr_vis_inv mu1 mu2); eassumption.
      apply eq_sym. apply restrictI_None.
        rewrite <- H4.
        destruct (restrictD_None' _ _ _ Heqd); clear Heqd.
          left; trivial.
        destruct H6 as [bb [dd [AI VIS]]].
          right. remember (vis mu1 b') as q.
          destruct q; trivial. apply eq_sym in Heqq.
          apply (intern_incr_vis mu1 mu2 H2) in Heqq. congruence. 
  red; intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inversion H. subst b0 sz0 id0. eapply Mem.perm_alloc_3; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_alloc_4; eauto. 
  exploit me_bounded; try eassumption. 
    (*idea why old proof unfold block in *; xomega. doesn't work here any more*)
    intros. destruct H7. clear - H8 RES. intros N; subst. xomega.
  red; intros. exploit PERM; eauto. intros [A|A]. auto. right. 
  inv A. apply is_reachable_intro with id0 b0 sz0 delta; auto.
  rewrite PTree.gso. auto. intros N; subst. rewrite H6 in H5. discriminate. 
    eapply intern_incr_restrict; eassumption.
  eapply H2. assumption.
  intros. eapply ME_INCR; try eassumption.
          exploit (H4 b0). subst b. intros N; subst. xomega. 
          unfold as_inj, join. rewrite H.
            destruct (disjoint_extern_local _ WD2 b0).
              assert (extern_of mu1 = extern_of mu2) by eapply H2. 
              rewrite H8, H7. 
              intros. rewrite <- H9; reflexivity. 
          rewrite H7 in H; discriminate.
  eapply (structured_match_callstack_intern_invariant mu1) with (m1 := m1); eauto. 
  intros. eapply Mem.perm_alloc_4; eauto. 
    (*no idea why old proof unfold block in *; xomega. doesn't work here any more*)
    intros N; subst. clear - LO H.  xomega.
  intros. apply H4. 
    (*no idea why old proof unfold block in *; xomega. doesn't work here any more*)
    intros N; subst. clear - LO H.  xomega. 
  intros. destruct (eq_block b0 b). 
  subst b0. rewrite H3 in H. inv H. xomegaContradiction. 
  rewrite H4 in H; auto.
Qed.

Section InternalCall.
Lemma MS_structured_match_callstack_alloc_variables_rec:
  forall tm sp tf cenv lenv te lo cs,
  Mem.valid_block tm sp ->
  fn_stackspace tf <= Int.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  alloc_variables e1 m1 vars e2 m2 ->
  forall mu,
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars (as_inj mu) sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  structured_match_callstack mu m1 tm
    (Frame (cenv_remove cenv vars) tf e1 lenv te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  REACH_closed m1 (vis mu) -> sm_valid mu m1 tm -> SM_wd mu ->
  Mem.inject (as_inj mu) m1 tm ->
  exists mu2,
    structured_match_callstack mu2 m2 tm
      (Frame cenv tf e2 lenv te sp lo (Mem.nextblock m2) :: cs)
      (Mem.nextblock m2) (Mem.nextblock tm)
  /\ Mem.inject (as_inj mu2) m2 tm
  /\ (*LENB: THIS IS NEW*) intern_incr mu mu2
(****************The following three conditions are new******************)
  /\ (forall b, Mem.valid_block m1 b -> as_inj mu2 b = as_inj mu b)
  /\ (forall b b' d', as_inj mu b = None -> as_inj mu2 b = Some (b',d') -> b' = sp)
  /\ sm_locally_allocated mu mu2 m1 tm m2 tm
  /\ SM_wd mu2 /\ sm_valid mu2 m2 tm
  /\ REACH_closed m2 (vis mu2)
  /\ forall mu', SM_wd mu' ->  intern_incr mu2 mu' -> sm_inject_separated mu2 mu' m2 tm -> 
                 sm_inject_separated mu2 mu' m1 tm.
Proof. 
  intros until cs; intros VALID REPRES STKSIZE STKPERMS.
  induction 1; intros mu NOREPET COMPAT SEP1 SEP2 UNBOUND MCS RC SMV WD MINJ.
  (* base case *)
  simpl in MCS. exists mu. intuition.
   apply intern_incr_refl. 
   congruence.
   apply sm_locally_allocatedChar.
     repeat split; try extensionality bb; simpl;
     try rewrite freshloc_irrefl; intuition.
  (* inductive case *)
  simpl in NOREPET. inv NOREPET.
  assert (SPlocal: locBlocksTgt mu sp = true).
    inv MCS; trivial. 
(* exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.nextblock_alloc; eauto. intros NB.*)
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit (alloc_left_mapped_sm_inject mu); try eassumption. 
    instantiate (1 := ofs). zify. omega. 
    intros. exploit STKSIZE; eauto. omega. 
    intros. apply STKPERMS. zify. omega.
    replace (sz - 0) with sz by omega. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. omega. 
  intros [mu2 [A [B [C [D [E [WD2 [LocAlloc2 RC2]]]]]]]].
  exploit (IHalloc_variables mu2); eauto; clear IHalloc_variables.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b b1); intros P.
    subst b. rewrite C in H5; inv H5. 
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto. 
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto. 
    omega.
    eapply SEP2. apply in_cons; eauto. eauto. 
    rewrite D in H5; eauto. eauto. auto. 
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib. 
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply structured_match_callstack_alloc_left with (mu1:=mu); try eassumption. 
    rewrite cenv_remove_gso; auto. 
    apply UNBOUND with sz; auto with coqlib.
  intros. destruct H1 as [mu3 [HF1 [HF2 [HF3 [HF4 [HF5 [HF6 [HF7 [HF8 [HF9 HF10]]]]]]]]]]. 
    exists mu3. split; trivial.
    split; trivial. 
    split. eapply intern_incr_trans; eassumption.
    split. intros.
        rewrite HF4.
         apply D.
           intros N; subst.
               eapply (Mem.fresh_block_alloc _ _ _ _ _ H H1).
           apply (Mem.valid_block_alloc _ _ _ _ _ H _ H1).
    split; intros.
       destruct (eq_block b b1); subst.
       apply intern_incr_as_inj in HF3; trivial. rewrite (HF3 _ _ _ C) in H2. inv H2. trivial.
       specialize (D _ n).
         rewrite <- D in H1. apply (HF5 _ _ _ H1 H2).
    split. apply sm_locally_allocatedChar. 
           apply sm_locally_allocatedChar in HF6.
           destruct HF6 as [AA [BB [CC [DD [EE FF]]]]].
           rewrite AA, BB, CC, DD, EE, FF. 
             clear AA BB CC DD EE FF. 
             clear HF1 HF2 HF4 HF5 HF8 HF9 HF10 RC2.
           apply sm_locally_allocatedChar in LocAlloc2.
           destruct LocAlloc2 as [AA [BB [CC [DD [EE FF]]]]].
           rewrite AA, BB, CC, DD, EE, FF. clear AA BB CC DD EE FF.
           apply alloc_forward in H. apply alloc_variables_forward in H0. 
           repeat split; extensionality bb; 
             try rewrite (freshloc_irrefl tm); simpl; intuition.
             rewrite <- orb_assoc. rewrite freshloc_trans; trivial.
             rewrite <- orb_assoc. rewrite freshloc_trans; trivial.
  intuition.
  destruct (HF10 _ H1 H2 H5) as [AA [BB CC]]. clear H5 HF10.
     split. intros.
       eapply AA; eassumption.
     split; intros.
        intros N. eapply BB; try eassumption.
        apply (Mem.valid_block_alloc _ _ _ _ _ H _ N).
      intros N. eapply CC; try eassumption.
Qed.

(*LENB: Lemma is modified - we need to put sp into locBlocksTgt mu*)
Lemma structured_match_callstack_alloc_right:
  forall mu cenv m tm cs tf tm' sp le te (WD: SM_wd mu) (SMV: sm_valid mu m tm),
  structured_match_callstack mu m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  Mem.inject (as_inj mu) m tm ->
  match_temps (restrict (as_inj mu) (vis mu)) le te ->
  (forall id, cenv!id = None) ->
  structured_match_callstack (alloc_right_sm mu sp) m tm'
      (Frame cenv tf empty_env le te sp (Mem.nextblock m) (Mem.nextblock m) :: cs)
      (Mem.nextblock m) (Mem.nextblock tm')
  /\ SM_wd (alloc_right_sm mu sp) /\ sm_valid (alloc_right_sm mu sp) m tm'.
Proof. 
  intros.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  assert (WD': SM_wd (alloc_right_sm mu sp)).
    apply alloc_right_sm_wd; trivial.
    remember (DomTgt mu sp) as d.
    destruct d; trivial. apply eq_sym in Heqd; subst.
    apply Mem.fresh_block_alloc in H0.
    elim H0. apply SMV. apply Heqd.
  assert (SMV': sm_valid (alloc_right_sm mu sp) m tm').
    split; intros bb HH.
      apply SMV; eassumption.
      unfold RNG in HH. rewrite alloc_right_sm_DomTgt in HH.
        apply orb_true_iff in HH; destruct HH.
          destruct (eq_block bb sp); try discriminate. subst.
          eapply Mem.valid_new_block; eassumption.
       eapply Mem.valid_block_alloc; try eassumption. 
         eapply SMV; eassumption.
  intuition.
  constructor.
  xomega.
  subst. rewrite NEXTBLOCK. unfold block in *; xomega.
  assumption.
  constructor; intros.
    rewrite H3. rewrite PTree.gempty. constructor.
    xomega.
    rewrite PTree.gempty in H4; discriminate.
    destruct (restrictD_Some _ _ _ _ _ H4).
    eelim Mem.fresh_block_alloc; eauto. eapply Mem.valid_block_inject_2; eauto.
  red; intros. rewrite PTree.gempty in H4. discriminate.
  red; intros. left. eapply Mem.perm_alloc_2; eauto.

  unfold alloc_right_sm; simpl. 
    destruct (eq_block sp sp); try reflexivity. congruence. 

  intros. 
     rewrite alloc_right_sm_local in H4. subst.
     eapply SMV. apply local_in_all in H4; trivial. 
        eapply as_inj_DomRng; eassumption.

  subst. 
    eapply (structured_match_callstack_intern_invariant mu)
     with (tm1 := tm); try eassumption.
    apply alloc_right_sm_intern_incr.
    intuition.
    intros. eapply Mem.perm_alloc_1; eauto.
    intros. rewrite alloc_right_sm_as_inj. trivial.
    rewrite alloc_right_sm_as_inj. trivial.
Qed.

Lemma MS_structured_match_callstack_alloc_variables_aux:
  forall tm1 sp tm2 m1 vars e m2 cenv mu (cs:callstack) fn lenv te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  REACH_closed m1 (vis mu) -> sm_valid mu m1 tm1 -> SM_wd mu ->
  Mem.inject (as_inj mu) m1 tm1 ->
  structured_match_callstack mu m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps (restrict (as_inj mu) (vis mu)) lenv te ->
  exists mu',
    structured_match_callstack mu' m2 tm2 (Frame cenv fn e lenv te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject (as_inj mu') m2 tm2
  /\ intern_incr mu mu'
(****************The following three conditions are new******************)
(* In the third clause, we now step from  m' to m, and also from f' to f and from tm' to tm******************)
  /\ (forall b, Mem.valid_block m1 b -> (as_inj mu') b = (as_inj mu) b)
  /\ (forall b b' d', as_inj mu b = None -> as_inj mu' b = Some (b',d') -> b' = sp)
  /\ sm_locally_allocated mu mu' m1 tm1 m2 tm2
  /\ SM_wd mu' /\ sm_valid mu' m2 tm2
  /\ REACH_closed m2 (vis mu')
  /\ forall mu'', SM_wd mu'' -> intern_incr mu' mu'' -> sm_inject_separated mu' mu'' m2 tm2 -> 
          sm_inject_separated mu mu'' m1 tm1.
Proof. clear core_data. 
  intros.
exploit (structured_match_callstack_alloc_right mu (cenv_remove cenv vars)); try eassumption.
     intros. destruct (In_dec peq id (map fst vars)).
     apply cenv_remove_gss; auto.
     rewrite cenv_remove_gso; auto.
     destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto. 
clear H10. intros [MC [WD1 SMV1]].
rewrite <- (alloc_right_sm_as_inj mu sp) in H9.
rewrite <- (alloc_right_sm_as_inj mu sp) in H11.
remember (alloc_right_sm mu sp) as mu1.
assert (AR: exists mu2,
   structured_match_callstack mu2 m2 tm2
                     (Frame cenv fn e lenv te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                     (Mem.nextblock m2) (Mem.nextblock tm2) 
 
  /\ Mem.inject (as_inj mu2) m2 tm2
  /\ intern_incr mu1 mu2
  /\ (forall b, Mem.valid_block m1 b -> as_inj mu2 b = as_inj mu1 b)
  /\ (forall b b' d', as_inj mu1 b = None -> as_inj mu2 b = Some (b',d') -> b' = sp)
  /\ sm_locally_allocated mu1 mu2 m1 tm2 m2 tm2
  /\ SM_wd mu2 /\ sm_valid mu2 m2 tm2
  /\ REACH_closed m2 (vis mu2)
  /\ forall mu', SM_wd mu' -> intern_incr mu2 mu' ->
                 sm_inject_separated mu2 mu' m2 tm2 -> 
                 sm_inject_separated mu2 mu' m1 tm2).
  eapply MS_structured_match_callstack_alloc_variables_rec; eauto with mem.
  (*instantiate (1 := f1).*) red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto. 
  intros. apply PTree.gempty.
  subst mu1. unfold alloc_right_sm, vis; simpl. assumption.
  subst mu1. eapply Mem.alloc_right_inject; eassumption. 

destruct AR as [mu2 [MC2 [INJ2 [INC2 [AI2 [SP2
     [LocAlloc2 [WD2 [SMV2 [RC2 SEP2]]]]]]]]]].
exists mu2; intuition.
eapply intern_incr_trans; try eassumption.
  subst mu1. apply alloc_right_sm_intern_incr.
rewrite (AI2 _ H10). subst mu1.
  rewrite alloc_right_sm_as_inj. trivial.
eapply SP2; try eassumption.
  subst mu1. rewrite alloc_right_sm_as_inj. trivial.
(*locally_allocated*)
  rewrite sm_locally_allocatedChar.
  rewrite sm_locally_allocatedChar in LocAlloc2.
  destruct LocAlloc2 as [AA [BB [CC [DD [EE FF]]]]].
  rewrite AA, BB, CC, DD, EE, FF. clear AA BB CC DD EE FF.
  subst mu1. try rewrite alloc_right_sm_DomSrc, alloc_right_sm_DomTgt, 
     alloc_right_sm_locBlocksTgt.
  intuition.
  extensionality bb. rewrite (freshloc_irrefl tm2).
    rewrite (freshloc_alloc _ _ _ _ _ H). 
    rewrite <- orb_assoc. rewrite orb_false_r.
    rewrite orb_comm. trivial.
  extensionality bb. rewrite (freshloc_irrefl tm2).
    rewrite (freshloc_alloc _ _ _ _ _ H). 
    rewrite <- orb_assoc. rewrite orb_false_r.
    rewrite orb_comm. trivial.
(*sm_inject_separated*) 
 split. intros b; intros.
   assert (X: as_inj mu1 b = None).
     subst mu1. rewrite alloc_right_sm_as_inj. assumption.
   remember (as_inj mu2 b) as z; destruct z; apply eq_sym in Heqz.
  (*Some p*) destruct p as [bb zz].
             specialize (SP2 _ _ _ X Heqz). subst.
             rewrite (intern_incr_as_inj _ _ H12 H10 _ _ _ Heqz) in H15. inv H15.
             split.
               remember (DomSrc mu b) as q.
               destruct q; trivial; apply eq_sym in Heqq.
               rewrite (AI2 b) in Heqz. congruence.
               eapply H7. apply Heqq.
             remember (DomTgt mu b2) as q.
              destruct q; trivial; apply eq_sym in Heqq.
              apply Mem.fresh_block_alloc in H.
              elim H. apply H7. apply Heqq.
   (*None*) assert (DomSrc mu2 b = false /\ DomTgt mu2 b2 = false).
               eapply H13; eassumption.
            destruct H16; clear SEP2 H13.
            apply sm_locally_allocatedChar in LocAlloc2. destruct LocAlloc2 as [DS [DT _]].
            rewrite DS in H16. rewrite DT in H17; clear DS DT.
            subst mu1. rewrite alloc_right_sm_DomSrc in H16.
               rewrite alloc_right_sm_DomTgt in H17.
            rewrite orb_false_iff in *.
            rewrite orb_false_iff in *.
            intuition.
specialize (SEP2 _ H10 H12 H13).
split; intros.
  remember (DomSrc mu2 b1) as q;
  destruct q; apply eq_sym in Heqq.
    apply sm_locally_allocatedChar in LocAlloc2. destruct LocAlloc2 as [DS _]. 
    rewrite DS in Heqq; clear DS.
    subst mu1. rewrite (alloc_right_sm_DomSrc), H14 in Heqq. simpl in Heqq.
    apply freshloc_charT in Heqq. apply Heqq.
  apply SEP2; assumption. 
remember (DomTgt mu2 b2) as q.
  destruct q; apply eq_sym in Heqq.
    apply sm_locally_allocatedChar in LocAlloc2. destruct LocAlloc2 as [_ [DT _]].
    rewrite DT in Heqq; clear DT.
    subst mu1. rewrite (alloc_right_sm_DomTgt), (freshloc_irrefl tm2), H14 in Heqq.
    destruct (eq_block b2 sp); subst; simpl in *; try discriminate. 
      eapply Mem.fresh_block_alloc; eassumption.
  assert (~ Mem.valid_block tm2 b2).
    eapply H13; assumption.
  intros N. apply H16. eapply Mem.valid_block_alloc; eassumption.
Qed.

Lemma MS_structured_match_callstack_alloc_variables:
  forall tm1 sp tm2 m1 vars e m2 cenv mu cs fn lenv te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  REACH_closed m1 (vis mu) -> sm_valid mu m1 tm1 -> SM_wd mu ->
  Mem.inject (as_inj mu) m1 tm1 ->
  structured_match_callstack mu m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps (restrict (as_inj mu) (vis mu)) lenv te ->
  exists mu',
    structured_match_callstack mu' m2 tm2 (Frame cenv fn e lenv te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject (as_inj mu') m2 tm2
  /\ intern_incr mu mu'
  /\ sm_inject_separated mu mu' m1 tm1
  /\ sm_locally_allocated mu mu' m1 tm1 m2 tm2
  /\ SM_wd mu' /\ sm_valid mu' m2 tm2
  /\ REACH_closed m2 (vis mu').
Proof. intros.
  exploit MS_structured_match_callstack_alloc_variables_aux;
      try eassumption.
  intros.
  destruct H12 as [mu' [MCS2 [INJ2 [INC [HH1 [HH2 [HH3 [HH4 [HH5 [HH6 HH7]]]]]]]]]].
  exists mu'; intuition.
  split.
    intros b; intros.
    specialize (HH2 _ _ _ H12 H13); subst.
    split. remember (DomSrc mu b) as dd.
           destruct dd; trivial; apply eq_sym in Heqdd.
           rewrite (HH1 b) in H13. congruence.
           apply H7. apply Heqdd.
        inv MCS2. remember (DomTgt mu sp) as dd.
           destruct dd; trivial; apply eq_sym in Heqdd.
           apply Mem.fresh_block_alloc in H.
           elim H. eapply H7. apply Heqdd.
    split; intros.
      eapply (HH7 mu'). trivial. apply intern_incr_refl. 
           apply sm_inject_separated_same_sminj. assumption. assumption. 
      eapply (HH7 mu'). trivial. apply intern_incr_refl. 
           apply sm_inject_separated_same_sminj. assumption. assumption.
Qed.  
          
Variable cenv : compilenv.
Variable f : Csharpminor.function.
Variable mu : SM_Injection.
Variable m tm : mem.
Variable cs : callstack.
Variable e : Csharpminor.env.
Variable lenv : temp_env.
Variable k : Csharpminor.cont.
Variable tk : cont.

Theorem MS_structured_match_callstack_function_entry:
  forall fn cenv tf m' tm' sp cs args targs,
  build_compilenv fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  list_norepet (map fst (Csharpminor.fn_vars fn)) ->
  list_norepet (Csharpminor.fn_params fn) ->
  list_disjoint (Csharpminor.fn_params fn) (Csharpminor.fn_temps fn) ->
  alloc_variables Csharpminor.empty_env m (Csharpminor.fn_vars fn) e m' ->
  bind_parameters (Csharpminor.fn_params fn) args (create_undef_temps fn.(fn_temps)) = Some lenv ->
  val_list_inject (restrict (as_inj mu) (vis mu)) args targs ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  structured_match_callstack mu m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  REACH_closed m (vis mu) -> sm_valid mu m tm -> SM_wd mu ->
  Mem.inject (as_inj mu) m tm ->
  let te := set_locals (Csharpminor.fn_temps fn) (set_params targs (Csharpminor.fn_params fn)) in
  exists mu',
     structured_match_callstack mu' m' tm'
                     (Frame cenv tf e lenv te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject (as_inj mu') m' tm' 
  /\ intern_incr mu mu'
  /\ sm_inject_separated mu mu' m tm
  /\ sm_locally_allocated mu mu' m tm m' tm'
  /\ SM_wd mu' /\ sm_valid mu' m' tm'
  /\ REACH_closed m' (vis mu').
Proof.
  intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply MS_structured_match_callstack_alloc_variables; try eassumption.   
  intros. eapply build_compilenv_domain; eauto. 
  eapply bind_parameters_agree; eassumption.
Qed.

End InternalCall.

Lemma orb_same: forall b b', b = b || b && b'.
Proof. intros. destruct b; intuition. Qed.

Lemma andb_same: forall b b' (HBb': b=true -> b'= true), b = b && b'.
Proof. intros. destruct b; intuition. Qed.

Lemma EFF_switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall f sp e m,
     effstep_plus (cmin_eff_sem hf) tge EmptyEffect
         (CMin_State f s k sp e) m (CMin_State f body k' sp e) m).
Proof.
  induction ls; intros.
(*1*) 
  monadInv H.
  eexists; split.
      econstructor; eauto.
  intros. eapply effstep_plus_trans'. 
            apply effstep_plus_one.
              constructor. 
              apply effstep_plus_one.
                constructor.
              extensionality b; extensionality z.
                apply orb_same.
(*2*)
  monadInv H. exploit IHls; eauto. intros [k' [A B]]. 
  eexists; split.
      econstructor; eauto.
  intros. eapply effstep_plus_star_trans'. eauto. 
  eapply effstep_star_trans. 
      apply effstep_star_one.
        constructor. 
        apply effstep_star_one.
          constructor.
        extensionality b; extensionality z.
                apply orb_same.
Qed.

Lemma EFF_switch_ascent:
  forall f n sp e m cenv xenv k ls k1,
  let tbl := switch_table ls O in
  let ls' := select_switch n ls in
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  effstep_star (cmin_eff_sem hf) tge EmptyEffect 
    (CMin_State f (Sexit (Switch.switch_target n (length tbl) tbl)) k1 sp e) m  
    (CMin_State f (Sexit O) k2 sp e) m
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction ls; intros; unfold tbl, ls'; simpl.
(*1*)
  inv H. 
  eexists; split.
     apply effstep_star_zero.
     econstructor; eauto.
(*2*)
  simpl in H. inv H. 
  rewrite Int.eq_sym. destruct (Int.eq i n).
  econstructor; split.
    apply effstep_star_zero.
    econstructor; eauto. 
  exploit IHls; eauto. intros [k2 [A B]].
  rewrite (length_switch_table ls 1%nat 0%nat). 
  rewrite switch_table_shift.
  exists k2; split; try exact B.
  eapply effstep_star_trans'.
    eapply effstep_star_one.
      constructor. 
      eapply effstep_star_trans.
        eapply effstep_star_one.
          econstructor. 
          apply A.
      extensionality b; extensionality z.
                apply orb_same. 
Qed.

Lemma eff_make_store_correct:
  forall f sp te tm addr tvaddr rhs tvrhs chunk m vaddr vrhs m' fn k,
  eval_expr tge sp te tm addr tvaddr ->
  eval_expr tge sp te tm rhs tvrhs ->
  Mem.storev chunk m vaddr vrhs = Some m' ->
  Mem.inject f m tm ->
  val_inject f vaddr tvaddr ->
  val_inject f vrhs tvrhs ->
  exists tm', exists tvrhs',
  cmin_effstep hf tge (StoreEffect tvaddr (encode_val chunk tvrhs')) (CMin_State fn (make_store chunk addr rhs) k sp te) tm
        (CMin_State fn Sskip k sp te) tm'
  /\ Mem.storev chunk tm tvaddr tvrhs' = Some tm'
  /\ Mem.inject f m' tm'.
Proof.
  intros. unfold make_store.
  exploit eval_store_arg. eexact H0. eauto. 
  intros [tv [EVAL VCINJ]].
  exploit storev_mapped_content_inject; eauto.
  intros [tm' [STORE MEMINJ]].
  exists tm'; exists tv.
  split. eapply cmin_effstep_store; eauto.
  auto.
Qed.

Section EFFSTEP_DIAGRAM.
Variable cenv : compilenv.
Variable sz : Z.
Variable f : Csharpminor.function.
Variable tfn : function.
Variable mu : SM_Injection.
Variable m tm : mem.
Variable e : Csharpminor.env.
Variable lenv : temp_env.
Variable te : env.
Variable sp lo hi: Values.block.
Variable cs : callstack.
Variable s : Csharpminor.stmt.
Variable k : Csharpminor.cont.
Variable tk : cont.
Variable xenv : exit_env.
Variable PRE: REACH_closed m (vis mu) /\ 
      meminj_preserves_globals ge (as_inj mu) /\
      (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
      sm_valid mu m tm /\ SM_wd mu /\
      Mem.inject (as_inj mu) m tm.
Variable TRF : transl_funbody cenv sz f = OK tfn.

Lemma EFF_step_case_SkipSeq: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kseq s k) tk cenv xenv cs),
exists st2' : CMin_core, 
  exists m2' mu',
   effstep_plus (cmin_eff_sem hf) tge EmptyEffect
     (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm st2' m2' 
   /\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  MATCH (CSharpMin_State f s k e lenv) mu'
    (CSharpMin_State f s k e lenv) m st2' m2' /\
  SM_wd mu' /\ sm_valid mu' m m2'.
Proof. intros.
  dependent induction MK.

  eexists. eexists. exists mu. 
  split.
    apply effstep_plus_one.
        econstructor. 
  simpl. (* exists (CSharpMin_State f s k e le).
     left. *) intuition. 
    apply intern_incr_refl.
    apply gsep_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
      try rewrite freshloc_irrefl; intuition.
    split; intuition.
    eapply SMC_states; eauto. 

  eexists. eexists. exists mu. 
  split.
    apply effstep_plus_one.
      econstructor. 
   simpl. (*exists (CSharpMin_State f (Csharpminor.Sseq s1 s2) k e le).
      left.  *) intuition. 
    apply intern_incr_refl.
    apply gsep_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
      try rewrite freshloc_irrefl; intuition.
    split; intuition.
    eapply SMC_state_seq; eauto.

  exploit IHMK; eauto. clear IHMK. 
  intros [T2 [m2 [nu [A C]]]].
  exists T2. exists m2. exists nu. 
  split.
     eapply effstep_star_plus_trans'.
        apply effstep_star_one.
          constructor. 
     simpl. apply A. 
    extensionality b; extensionality z.
                apply orb_same.
  apply C.
Qed.

Lemma EFF_step_case_SkipBlock: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm)) 
(MK : match_cont (Csharpminor.Kblock k) tk cenv xenv cs),
exists st2' : CMin_core,
  exists m2' mu',
     effstep_plus (cmin_eff_sem hf) tge EmptyEffect
        (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm st2' m2'      
  /\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  MATCH (CSharpMin_State f Csharpminor.Sskip k e lenv) mu' (CSharpMin_State f Csharpminor.Sskip k e lenv) m st2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m m2'.
Proof. intros.
  dependent induction MK.

  eexists. eexists. exists mu. 
  split.
    apply effstep_plus_one.
      constructor. 
   simpl. (*exists (CSharpMin_State f Csharpminor.Sskip k e le).
      left.  *) intuition. 
    apply intern_incr_refl.
    apply gsep_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
      try rewrite freshloc_irrefl; intuition.
    split; intuition. 
    eapply SMC_states; eauto.

  exploit IHMK; eauto. clear IHMK.
  intros [T2 [m2 [nu [A C]]]].
  exists T2; exists m2; exists nu.
  split.
     eapply effstep_star_plus_trans'.
        apply effstep_star_one.
          constructor.
        simpl. apply A. 
    extensionality b; extensionality z.
                apply orb_same.
  (* simpl in *. exists c'.*) apply C.
Qed.

Lemma EFF_match_is_call_cont: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 v (MK: match_cont k tk cenv xenv cs)
   (CC: Csharpminor.is_call_cont k),
  exists tk',
    effstep_star (cmin_eff_sem hf) tge EmptyEffect
                (CMin_State tfn Sskip tk v te) tm
                (CMin_State tfn Sskip tk' v te) tm
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
Proof. intros MCS.
  induction 1; simpl; intros; try contradiction.
  econstructor; split.
     apply effstep_star_zero. split. exact I. econstructor; eauto.
  exploit IHMK; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply effstep_star_trans'; eauto.
     apply effstep_star_one. constructor.
     extensionality b; extensionality z.
                apply orb_same.
    auto.
  econstructor; split.
     apply effstep_star_zero. split. exact I.
  econstructor; eauto.
Qed.

Lemma EFF_step_case_SkipCall: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm)) m'
(CC: Csharpminor.is_call_cont k)
(FL: Mem.free_list m (blocks_of_env e) = Some m')
(MK : match_cont k tk cenv xenv cs),
exists st2' : CMin_core,
  exists m2' mu',
    effstep_plus (cmin_eff_sem hf) tge (FreeEffect tm 0 (fn_stackspace tfn) sp)
      (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm st2' m2'      
  /\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m' m2' /\
  MATCH (CSharpMin_Returnstate Vundef k) mu' (CSharpMin_Returnstate Vundef k) m' st2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m' m2'.
Proof. intros.
  exploit EFF_match_is_call_cont; eauto. intros [tk' [A [B C]]]. 
  exploit match_callstack_freelist; eauto. eapply PRE. eapply PRE.
  intros [tm' [P [Q R]]].

  eexists. eexists. exists mu. 
  split. 
    eapply effstep_star_plus_trans'.
      (*eapply effstep_star_sub_val.*) apply A. 
      apply effstep_plus_one. apply cmin_effstep_skip_call; eassumption.
      extensionality b; extensionality z.
        unfold EmptyEffect; simpl.
       apply andb_same. intros. apply FreeEffect_validblock in H.
          destruct (valid_block_dec tm b); trivial; contradiction.
  assert (SMV': sm_valid mu m' tm').
    split; intros.
      assert (Mem.valid_block m b1).
        eapply PRE; eassumption.
      apply nextblock_freelist in FL.
      red. rewrite FL. apply H0. 
    apply (Mem.valid_block_free_1 _ _ _ _ _ P).
        destruct PRE as [_ [_ [_ [? _]]]].
        eapply H0. eassumption.      
  intuition; simpl. apply intern_incr_refl.
    apply gsep_refl.
    apply sm_inject_separated_same_sminj.
    simpl. apply sm_locally_allocatedChar.
       apply freshloc_free in P.
       apply freshloc_free_list in FL. 
       repeat split; extensionality b;
         try rewrite P; try rewrite FL; intuition.
    econstructor; eauto.
      econstructor; eauto.
    intuition.
 eapply REACH_closed_freelist; try eassumption.
Qed.

Lemma EFF_step_case_Assign: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 a v id x x0
(EE: Csharpminor.eval_expr ge e lenv m a v)
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0)),
exists st2' : CMin_core,
  exists m2' mu',
    effstep_plus (cmin_eff_sem hf) tge EmptyEffect
       (CMin_State tfn (Sassign id x) tk (Vptr sp Int.zero) te) tm st2' m2'
  /\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  MATCH (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv))
              mu' (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) m st2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m m2'.
Proof. intros.
  exploit transl_expr_correct. eapply PRE. eapply PRE.
     eassumption. eassumption. eassumption.
  intros [tv [EVAL [VINJ APP]]].
(*
  exploit var_set_correct; eauto. 
  intros [te' [tm' [EXEC [MINJ' [MCS' OTHER]]]]].
*)
  eexists. eexists. exists mu.
  split.
      apply effstep_plus_one. 
        constructor. eassumption.
  intuition; simpl.
    apply intern_incr_refl.
    apply gsep_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
      try rewrite freshloc_irrefl; intuition.
    split; intuition.
clear H H0 H2 H3.
inv MCS.
econstructor; try eassumption. reflexivity.
econstructor; try eassumption.
eapply match_temps_assign; assumption.
Qed.


Lemma EFF_step_case_Store: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
  x x0 x1 x2 chunk m' a addr vaddr v
(CH: Mem.storev chunk m vaddr v = Some m')
(MK : match_cont k tk cenv xenv cs)
(EvAddr : Csharpminor.eval_expr ge e lenv m addr vaddr)
(EvA : Csharpminor.eval_expr ge e lenv m a v)
(EQ : transl_expr cenv addr = OK (x, x0))
(EQ1 : transl_expr cenv a = OK (x1, x2)),
(*exists tv,
   (eval_expr tge (Vptr sp Int.zero) te tm x1 tv /\
   val_inject (restrict (as_inj mu) (vis mu)) v tv /\ 
   val_match_approx x2 v) /\*)
exists tv',
   (eval_expr tge (Vptr sp Int.zero) te tm x tv' /\
   val_inject (restrict (as_inj mu) (vis mu)) vaddr tv' /\
   val_match_approx x0 vaddr) /\
exists st2' : CMin_core,
  exists m2' mu',
exists vv, 
       effstep_plus (cmin_eff_sem hf) tge (StoreEffect tv' (encode_val chunk vv))
          (CMin_State tfn (make_store chunk x x1) tk 
          (Vptr sp Int.zero) te) tm st2' m2' /\ 
  Mem.storev chunk tm tv' vv = Some m2' /\
  intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m' m2' /\
  MATCH (CSharpMin_State f Csharpminor.Sskip k e lenv)
              mu' (CSharpMin_State f Csharpminor.Sskip k e lenv) m' st2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m' m2'.
Proof. intros.
  exploit transl_expr_correct. eapply PRE. eapply PRE. eassumption. eexact EvA. eassumption.
  intros [tv2 [EVAL2 [VINJ2 APP2]]].
(*  exists tv2. repeat (split; try assumption).*)
  exploit transl_expr_correct. eapply PRE. eapply PRE. eassumption. eexact EvAddr.  eassumption.
  intros [tv1 [EVAL1 [VINJ1 APP1]]].
  exists tv1. repeat (split; try assumption).
  exploit eff_make_store_correct. eexact EVAL1. eexact EVAL2. eauto. eapply PRE.
     eapply val_inject_restrictD; try eassumption. 
     eapply val_inject_restrictD; try eassumption.
  intros [tm' [tv' [EXEC [STORE' MINJ']]]].
  eexists. eexists. exists mu, tv'.  
  split. apply effstep_plus_one. 
           eapply EXEC. 
  assert (SMV': sm_valid mu m' tm').
    destruct PRE as [_ [_ [_ [SMV _]]]].
    split; intros. 
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
  intuition; simpl.
    apply intern_incr_refl.
    apply gsep_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
      try rewrite (storev_freshloc _ _ _ _ _ STORE'); 
      try rewrite (storev_freshloc _ _ _ _ _ CH); intuition.
    econstructor; try eassumption.
    inv VINJ1; simpl in CH; try discriminate. 
    inv MCS. econstructor; try eassumption. reflexivity.
    econstructor; try eassumption.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ CH). assumption.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE'). assumption.
      eapply match_bounds_invariant; try eassumption.
        intros. eapply Mem.perm_store_2; eassumption.  
      eapply padding_freeable_invariant; try eassumption.
        intros.  eapply Mem.perm_store_1; eassumption.
      intros. trivial.
    eapply structured_match_callstack_intern_invariant; try eassumption.
      apply intern_incr_refl.
      intros. eapply Mem.perm_store_2; eassumption.
      intros. eapply Mem.perm_store_1; eassumption.
      trivial.
      trivial.
    intuition.
   destruct vaddr; inv CH.
     eapply REACH_Store; try eassumption.
       inv VINJ1. apply (restrictD_Some _ _ _ _ _ H8).
     intros b' Hb'. rewrite getBlocksD, getBlocksD_nil in Hb'.
       destruct v; inv Hb'. rewrite orb_false_r in H7.
       rewrite H7. simpl.
       assert (b0=b').
       remember (eq_block b0 b') as d.
          destruct d; intuition.
       subst. inv VINJ2. apply (restrictD_Some _ _ _ _ _ H9).
Qed. 

Lemma EFF_step_case_Call: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 x x0 x1 a vf fd optid vargs bl
(MK : match_cont k tk cenv xenv cs)
(EvalA: Csharpminor.eval_expr ge e lenv m a vf)
(EvalBL: Csharpminor.eval_exprlist ge e lenv m bl vargs)
(FF: Genv.find_funct ge vf = Some fd)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_exprlist cenv bl = OK x1),
exists c2' : CMin_core,
  exists m2' mu',
        effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
             (CMin_State  tfn (Scall optid (Csharpminor.funsig fd) x x1) tk (Vptr sp Int.zero) te) tm c2' m2'
/\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  MATCH (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv k)) mu'
              (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv k)) m c2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m m2'.
Proof. intros.
  simpl in FF.
  exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  exploit transl_expr_correct; try eassumption; try eapply PRE. intros [tvf [EVAL1 [VINJ1 APP1]]].
  assert (tvf = vf).
    exploit structured_match_callstack_match_globalenvs; eauto. intros [bnd MG].
    eapply val_inject_function_pointer; eauto.
    eapply  MG. 
  subst tvf.
  exploit transl_exprlist_correct; try eassumption. apply PRE. apply PRE.
  intros [tvargs [EVAL2 VINJ2]].
  eexists; eexists; exists mu. 
  split. apply effstep_plus_one.
           eapply cmin_effstep_call. eassumption. eassumption. apply FIND.
                      eapply sig_preserved; eauto.
  intuition; simpl.
    apply intern_incr_refl.
    apply gsep_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
      try rewrite freshloc_irrefl; intuition.
    split; intuition.
simpl. 
econstructor; try eassumption.
   eapply match_Kcall with (cenv' := cenv); eauto.
   simpl. trivial.
Qed.


Lemma EFF_step_case_Ite: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 x x0 x1 x2 b v a s1 s2
(H : Csharpminor.eval_expr ge e lenv m a v)
(BoolOfVal : Val.bool_of_val v b)
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_stmt cenv xenv s1 = OK x1)
(EQ0 : transl_stmt cenv xenv s2 = OK x2),
exists c2' : CMin_core,
  exists m2' mu',
     effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
     (CMin_State tfn (Sifthenelse x x1 x2) tk (Vptr sp Int.zero) te) tm c2' m2' /\
     intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  MATCH  (CSharpMin_State f (if b then s1 else s2) k e lenv) mu'
             (CSharpMin_State f (if b then s1 else s2) k e lenv) m c2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m m2'.
Proof. intros.
  exploit transl_expr_correct; try eassumption. apply PRE. apply PRE.
  intros [tv [EVAL [VINJ APP]]].
  exists (CMin_State tfn (if b then x1 else x2) tk (Vptr sp Int.zero) te).
  exists tm. exists mu. intuition.
     apply effstep_plus_one.
       eapply cmin_effstep_ifthenelse; eauto. eapply bool_of_val_inject; eauto.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.
    split; intuition.
     econstructor; eauto.
       destruct b; auto.
Qed.

Lemma EFF_step_case_Loop: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 x s
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_stmt cenv xenv s = OK x),
exists c2' : CMin_core,
  exists m2' mu',
     effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
     (CMin_State tfn (Sloop x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
     intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  MATCH (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) k) e lenv) mu'
             (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) k) e lenv) m c2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m m2'.
Proof. intros.
  eexists; eexists; exists mu.
  split.
     apply effstep_plus_one.
       econstructor; eauto.
  simpl in *. intuition.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.
    split; intuition.
     econstructor; eauto.
       econstructor; eauto. simpl. rewrite EQ; auto. 
Qed.

Lemma EFF_step_case_Block: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 x s
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_stmt cenv (true :: xenv) s = OK x),
exists c2' : CMin_core,
  exists m2' mu',
      effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
         (CMin_State tfn (Sblock x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
  intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
        MATCH (CSharpMin_State f s (Csharpminor.Kblock k) e lenv) mu' 
                    (CSharpMin_State f s (Csharpminor.Kblock k) e lenv) m c2' m2'
  /\ SM_wd mu' /\
  sm_valid mu' m m2'.
Proof. intros.
  eexists; eexists; exists mu; split.
     apply effstep_plus_one.
       econstructor; eauto.
  simpl in *. intuition.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.
    split; intuition.
     econstructor; eauto.
       econstructor; eauto. 
Qed.

Lemma EFF_step_case_ExitSeq: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 n s
(MK : match_cont (Csharpminor.Kseq s k) tk cenv xenv cs),
exists c2' : CMin_core,
  exists m2' mu',
       effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
               (CMin_State tfn (Sexit (shift_exit xenv n)) tk (Vptr sp Int.zero) te) tm c2' m2'  /\
        MATCH (CSharpMin_State f (Csharpminor.Sexit n) k e lenv) mu'
    (CSharpMin_State f (Csharpminor.Sexit n) k e lenv) m c2' m2'
/\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  SM_wd mu' /\ sm_valid mu' m m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; exists mu; split. 
     apply effstep_plus_one.
       econstructor; eauto.
  simpl in *; intuition.
      split; intuition.
      econstructor; eauto. reflexivity.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.

  exploit IHMK; eauto. intros [c2' [m2' [mu' [A B]]]].
  exists c2'. exists m2'. exists mu'. 
  split; auto. 
     eapply effstep_plus_trans'. 
       apply effstep_plus_one.
         constructor.
       simpl. apply A.
     extensionality b; extensionality z. 
       apply orb_same.

  exploit IHMK; eauto.  intros [c2' [m2' [mu' [A B]]]].
  exists c2'. exists m2'. exists mu'.
  split; auto. 
     eapply effstep_plus_trans'. 
         apply effstep_plus_one.
           constructor. 
         simpl. apply A.
     extensionality b; extensionality z. 
       apply orb_same.
Qed.

Lemma EFF_step_case_ExitBlockZero: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kblock k) tk cenv xenv cs),
exists c2' : CMin_core,
  exists m2' mu',
   effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
     (CMin_State tfn (Sexit (shift_exit xenv 0)) tk (Vptr sp Int.zero) te) tm c2' m2'
  /\ MATCH (CSharpMin_State f Csharpminor.Sskip k e lenv) mu'
    (CSharpMin_State f Csharpminor.Sskip k e lenv) m c2' m2'
/\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  SM_wd mu' /\ sm_valid mu' m m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; exists mu; split.
     apply effstep_plus_one. 
       constructor.
  simpl in *; intuition.
    econstructor; eauto.
      econstructor; eauto.
      intuition.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.

  exploit IHMK; eauto. intros [c2' [m2' [mu' [A B]]]].
  exists c2'. exists m2', mu'. 
  split; auto. 
     eapply effstep_plus_trans'. 
         apply effstep_plus_one.
           constructor. 
         simpl. apply A.
     extensionality b; extensionality z. 
       apply orb_same.
Qed.

Lemma EFF_step_case_ExitBlockNonzero: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 n (MK : match_cont (Csharpminor.Kblock k) tk cenv xenv cs),
exists c2' : CMin_core,
  exists m2' mu',
       effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
     (CMin_State tfn (Sexit (shift_exit xenv (S n))) tk (Vptr sp Int.zero) te) tm c2' m2' /\ 
       MATCH (CSharpMin_State f (Csharpminor.Sexit n) k e lenv) mu'
    (CSharpMin_State f (Csharpminor.Sexit n) k e lenv) m c2' m2'
/\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  SM_wd mu' /\ sm_valid mu' m m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; exists mu; split.
     apply effstep_plus_one.
       constructor.
  simpl in *; intuition.
    econstructor; eauto. 
      econstructor; eauto. auto.
    intuition.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.

  exploit IHMK; eauto. intros [c2' [m2' [mu' [A B]]]].
  exists c2'. exists m2', mu'. 
  split; auto. 
     eapply effstep_plus_trans'. 
       apply effstep_plus_one.
         constructor. 
         simpl. apply A.
     extensionality b; extensionality z. 
       apply orb_same.
Qed.

Lemma EFF_switch_MSI: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 ts ls body tk'
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S, exists m2' mu',
  effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
      (CMin_State tfn (Sexit O) tk' (Vptr sp Int.zero) te) tm S m2'
  /\ MATCH (CSharpMin_State f (seq_of_lbl_stmt ls) k e lenv) mu'
                 (CSharpMin_State f (seq_of_lbl_stmt ls) k e lenv) m
                 S m2'
  /\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  SM_wd mu' /\ sm_valid mu' m m2'.
Proof.
  intros. destruct ls; simpl.
(*1*)
  inv TK. eexists; eexists; exists mu; split. 
     eapply effstep_plus_trans'.
         eapply effstep_plus_one.
           constructor.
           simpl. eapply effstep_plus_one.
                   constructor.
         extensionality b; extensionality z. 
           apply orb_same. 
    intuition. econstructor; eauto. econstructor; eauto.
    intuition.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.
(*2*) 
  inv TK. econstructor; eexists; exists mu; split.
     eapply effstep_plus_trans'.
         eapply effstep_plus_one.
           constructor. 
           simpl. eapply effstep_plus_one.
                    constructor.
         extensionality b; extensionality z. 
           apply orb_same. 
     simpl; split. split. eapply SMC_state_seq; try eassumption.
          simpl. eapply  switch_match_cont; eauto. 
          intuition.
     intuition.
     apply intern_incr_refl.
    apply gsep_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl;
       try rewrite freshloc_irrefl; intuition.
Qed.

Lemma EFF_step_case_Switch: forall 
(MCS : structured_match_callstack mu m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m)
               (Mem.nextblock tm))
 a x x0 ts cases n
(MK : match_cont k tk cenv xenv cs)
(EvalA: Csharpminor.eval_expr ge e lenv m a (Vint n))
(EQ : transl_expr cenv a = OK (x, x0))
(EQ0 : transl_lblstmt cenv (switch_env cases xenv) cases
        (Sswitch x (switch_table cases 0) (length (switch_table cases 0))) =
      OK ts),
exists c2' : CMin_core,
  exists m2' mu',
       effstep_plus (cmin_eff_sem hf) tge EmptyEffect 
             (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm c2' m2' /\
         MATCH (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e lenv) mu'
    (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e lenv) m c2' m2'
/\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m m2' /\
  SM_wd mu' /\ sm_valid mu' m m2'.
Proof. intros.
  exploit transl_expr_correct; try eassumption. eapply PRE. eapply PRE.
  intros [tv [EVAL [VINJ APP]]].
  inv VINJ.
  exploit EFF_switch_descent; eauto. intros [k1 [A B]].
  exploit EFF_switch_ascent; eauto. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. simpl. intros [body' [ts' E]].
  exploit EFF_switch_MSI; eauto. intros [T2 [m2' [mu' [F [G HH]]]]].
  exists T2; exists m2'; exists mu'; split.
      eapply effstep_plus_star_trans'.
        eapply B. 
      eapply effstep_star_trans.
         eapply effstep_star_one.
           constructor. eassumption. 
      simpl.
        eapply effstep_star_trans.
         apply C.
         eapply effstep_plus_star. eapply F.
      extensionality b; extensionality z.  
        apply orb_same.
  intuition.
Qed.

Lemma MS_step_case_Builtin_eff:
forall x t ef optid vres m' bl vargs tvargs
(EvalArgs: Csharpminor.eval_exprlist ge e lenv m bl vargs)
(ExtCall: Events.external_call ef ge vargs m t vres m')
(MCS : structured_match_callstack mu m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(EQ : transl_exprlist cenv bl = OK x)
(MK : match_cont k tk cenv xenv cs)
(Vinj: val_list_inject (restrict (as_inj mu) (vis mu)) vargs tvargs)
(EVAL2: eval_exprlist tge (Vptr sp Int.zero) te tm x tvargs)
(OBS: ~ observableEF hf ef),
exists c2' : CMin_core,
  exists m2' mu', 
      effstep_plus (cmin_eff_sem hf) tge (BuiltinEffect tge ef tvargs tm)
           (CMin_State tfn (Sbuiltin optid ef x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
  intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m' m2' /\
  MATCH
    (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)) mu'
    (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)) m'
    c2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m' m2'.
Proof. intros. (*
  exploit transl_exprlist_correct; try eassumption; try eapply PRE. 
  intros [tvargs [EVAL2 VINJ2]].*)
  exploit structured_match_callstack_match_globalenvs; try eassumption.
  intros [hi' [Hi1 [Hi2 MG]]].
  exploit (inlineable_extern_inject ge tge); try eapply PRE.
      apply GDE_lemma. apply symbols_preserved. 
      eassumption. eassumption. eassumption. eassumption.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [GSEP [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]]].
  eexists; eexists; eexists; split.
      apply effstep_plus_one.
           econstructor; try eassumption.
(*             eapply Events.external_call_symbols_preserved; eauto.*)
      split. eassumption. intuition.
  exploit structured_match_callstack_builtin_invariant.
     Focus 3. eassumption. eassumption. eassumption. eassumption.
       instantiate (1:=m'). intros. eapply external_call_max_perm; eassumption.
       eassumption.
     intros. remember (as_inj mu b) as AI.
       destruct AI; apply eq_sym in HeqAI.
         destruct p. eapply intern_incr_as_inj; eassumption.
       remember (as_inj mu' b) as AI'.
         destruct AI'; apply eq_sym in HeqAI'; trivial.
         destruct p. destruct SEPARATED as [SEP1 [SEP2 SEP3]].
           destruct (SEP1 _ _ _ HeqAI HeqAI').
           elim (SEP2 _ H6). eapply as_inj_DomRng; eassumption. assumption.
     intros. remember (as_inj mu b) as AI.
       destruct AI; apply eq_sym in HeqAI.
         destruct p. apply intern_incr_as_inj in INCR. apply INCR in HeqAI. 
          rewrite HeqAI in H4; trivial. trivial.
       destruct SEPARATED as [SEP1 [SEP2 SEP3]].
           destruct (SEP1 _ _ _ HeqAI H4).
           elim (SEP3 _ H8). eapply as_inj_DomRng; eassumption. assumption. 
  inv MCS. intros.
  split. 
  assert (MCS': structured_match_callstack mu' m' tm'
                (Frame cenv tfn e lenv te sp lo hi :: cs)
                (Mem.nextblock m') (Mem.nextblock tm')).
    eapply structured_match_callstack_incr_bound. eassumption. 
    eapply external_call_nextblock; eauto.
    eapply external_call_nextblock; eauto.
  econstructor; try eassumption. eauto.
Opaque PTree.set.
  unfold set_optvar. destruct optid; simpl. 
  eapply structured_match_callstack_set_temp; eauto.
    assumption.

exploit (intern_incr_meminj_preserves_globals_as_inj ge).
  eapply H3. intuition. eapply WD'. assumption.
intuition.
Qed.
End EFFSTEP_DIAGRAM.

Section EFF_InternalCall.
Variable cenv : compilenv.
Variable f : Csharpminor.function.
Variable mu : SM_Injection.
Variable m tm : mem.
Variable cs : callstack.
Variable e : Csharpminor.env.
Variable lenv : temp_env.
Variable k : Csharpminor.cont.
Variable tk : cont.

Lemma EFF_step_case_InternalCall: forall 
(MCS : structured_match_callstack mu m tm cs (Mem.nextblock m)
        (Mem.nextblock tm))
(PRE: REACH_closed m (vis mu) /\ 
      meminj_preserves_globals ge (as_inj mu) /\
      (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
      sm_valid mu m tm /\ SM_wd mu /\
      Mem.inject (as_inj mu) m tm)
vargs targs x m1
(Param1: list_norepet (map fst (Csharpminor.fn_vars f)))
(Param2 : list_norepet (Csharpminor.fn_params f))
(Param3 : list_disjoint (Csharpminor.fn_params f) (fn_temps f))
(AlocVars : alloc_variables empty_env m (Csharpminor.fn_vars f) e m1)
(BindParams: bind_parameters (Csharpminor.fn_params f) vargs
       (create_undef_temps (fn_temps f)) = Some lenv)
(MK : match_cont k tk cenv nil cs)
(ISCC : Csharpminor.is_call_cont k)
(ARGSINJ : val_list_inject (restrict (as_inj mu) (vis mu)) vargs targs)
(EQ : transl_function f = OK x),
exists (c2' : CMin_core) m2' mu',
  effstep_plus (cmin_eff_sem hf) tge EmptyEffect
    (CMin_Callstate (AST.Internal x) targs tk) tm c2' m2'
 /\ intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m tm /\
  sm_locally_allocated mu mu' m tm m1 m2' /\ SM_wd mu' /\
  sm_valid mu' m1 m2' /\
  MATCH (CSharpMin_State f (Csharpminor.fn_body f) k e lenv) mu'
    (CSharpMin_State f (Csharpminor.fn_body f) k e lenv) m1 c2' m2'.
Proof. intros. 
  generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv f). intros ce sz BC.
  destruct (zle sz Int.max_unsigned).
  Focus 2. intros. exfalso. clear core_data.  congruence. 
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor.fn_sig f) 
                        (Csharpminor.fn_params f)
                        (Csharpminor.fn_temps f)
                        sz
                        x0) in *.
  caseEq (Mem.alloc tm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit MS_structured_match_callstack_function_entry; try eapply PRE; eauto.
    simpl; eauto.
    simpl; auto.
  intros [mu' [MCS2 [MINJ2 [IINCR [SEP [LOCALLOC [WD' [SMV' RC']]]]]]]].
  exists (CMin_State tf x0 tk (Vptr sp Int.zero)
     (set_locals (fn_temps f) (set_params targs (Csharpminor.fn_params f)))).
  exists tm', mu'.
  split.
    eapply effstep_plus_one. simpl. 
       econstructor. assumption. reflexivity. 
  intuition.
    solve[eapply intern_incr_globals_separate; eauto]. 
  split; intuition.
    econstructor. eexact TRBODY. eauto. eassumption.
    inv MK; simpl in ISCC; contradiction || econstructor; eauto.
  apply intern_incr_as_inj in IINCR; trivial.
    apply sm_inject_separated_mem in SEP; trivial.
    eapply meminj_preserves_incr_sep; eassumption. 
  assert (frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IINCR.
     rewrite <- H6. apply (H0 _ H4).  
Qed.
End EFF_InternalCall.

Lemma MATCH_effcore_diagram:
forall st1 m1 st1' m1' (U1 : Values.block -> Z -> bool)
       (EFFSTEP: effstep (csharpmin_eff_sem hf) ge U1 st1 m1 st1' m1')
       st2 mu m2
       (MC: MATCH st1 mu st1 m1 st2 m2),
exists st2' m2' mu',
  intern_incr mu mu' /\
   globals_separate ge mu mu' /\
  sm_inject_separated mu mu' m1 m2 /\
  sm_locally_allocated mu mu' m1 m2 m1' m2' /\
  MATCH st1' mu' st1' m1' st2' m2' /\
  (exists U2 : Values.block -> Z -> bool,
     (effstep_plus (cmin_eff_sem hf) tge U2 st2 m2 st2' m2' \/
      (MC_measure st1' < MC_measure st1)%nat /\
      effstep_star (cmin_eff_sem hf) tge U2 st2 m2 st2' m2') /\
     (forall 
       (UHyp: forall b ofs,  U1 b ofs = true -> vis mu b = true)
       b ofs, U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : Values.block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty))).
Proof.
intros. unfold core_data in *.
induction EFFSTEP; simpl in *.

{ (*skip seq*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      monadInv TR.
      destruct (EFF_step_case_SkipSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS MK) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'. 
      intuition.
      exists EmptyEffect. intuition. }
{ (*skip Block*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      monadInv TR.
      destruct (EFF_step_case_SkipBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS MK) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'. 
      intuition.
      exists EmptyEffect. intuition. }
{ (*skip Call*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      monadInv TR.
      destruct (EFF_step_case_SkipCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS _ H H0 MK) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'. 
      intuition.
      exists (FreeEffect m2 0 (fn_stackspace tfn) sp). intuition.
        apply FreeEffectD in H13. destruct H13 as [? [VB Arith]]; subst.
        inv MCS. unfold visTgt. rewrite SPlocal. trivial.
      apply FreeEffectD in H13. destruct H13 as [? [VB Arith]]; subst.
        inv MCS. rewrite H15 in SPlocal. discriminate. }
{ (*assign*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      monadInv TR.
      destruct (EFF_step_case_Assign _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS _ _ id _ _ H MK EQ) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'. 
      intuition.
      exists EmptyEffect. intuition. }
{ (*store*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      monadInv TR.
      destruct (EFF_step_case_Store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS _ _ _ _ _ _ _ _ _ _ H1 MK H H0 EQ EQ1)
       as [vv [Hvv [c2' [m2' [mu' [u [cstepPlus [STORE' MS]]]]]]]].
      exists c2'. exists m2'. exists mu'. 
      intuition.
      exists (StoreEffect vv (encode_val chunk u)).
      intuition.
      
      apply StoreEffectD in H17.
        destruct H17 as [i [VV Arith]]. subst.
        destruct vaddr; inv H1.
        inv H3.
        eapply visPropagateR; try eassumption.
        
      apply StoreEffectD in H17.
        destruct H17 as [i [VV Arith]]. subst.
        destruct vaddr; inv H1. 
        eapply StoreEffect_PropagateLeft; try eassumption.
        unfold StoreEffect.
        destruct (eq_block b b); simpl.
          destruct (zle (Int.unsigned i) ofs); simpl in *.
           destruct (zlt ofs (Int.unsigned i + Z.of_nat (length (encode_val chunk u)))); trivial.
           omega.
          omega.
        elim n. trivial. }
{  (*call*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      monadInv TR.
      destruct (EFF_step_case_Call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
       PRE TRF MCS _ _ _ _ _ _ optid vargs _ MK H H0 H1 EQ EQ1) 
        as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'. 
      intuition.
      exists EmptyEffect. intuition. }
{  (*builtin*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      monadInv TR.
      exploit transl_exprlist_correct; try eassumption. eapply PRE. eapply PRE.
      intros [tvargs [EVAL2 VINJ2]].
      exploit MS_step_case_Builtin_eff; try eassumption.
      intros [c2' [m2' [mu' [effstepPlus MS]]]]. assumption.
      instantiate (1:=optid) in effstepPlus.
      exists c2', m2', mu'. intuition. 
      exists (BuiltinEffect tge ef tvargs m2).
      split. left. assumption. 
      intros. eapply BuiltinEffect_Propagate; eassumption. }
{ (* seq *)
     destruct MC as [SMC PRE].
     inv SMC. 
      (*Case 1*) 
         monadInv TR.
         exists  (CMin_State tfn x (Kseq x0 tk) (Vptr sp Int.zero) te). 
         exists m2. 
         exists mu. intuition. 
                apply intern_incr_refl.
    apply gsep_refl.
                apply sm_inject_separated_same_sminj.
                apply sm_locally_allocatedChar.
                  repeat split; extensionality b;  
                  try rewrite freshloc_irrefl; intuition.
                econstructor; eauto.
                  econstructor; eauto.
                  econstructor; eauto.
                  intuition. 
         exists EmptyEffect. 
         intuition. left. simpl.
               eapply effstep_plus_one.  
                 econstructor; eauto. 
      (* seq 2 *) 
         exists (CMin_State tfn ts1 tk (Vptr sp Int.zero) te).
         exists m2; exists mu. intuition. 
                apply intern_incr_refl.
    apply gsep_refl.
                apply sm_inject_separated_same_sminj.
                apply sm_locally_allocatedChar.
                  repeat split; extensionality b;  
                  try rewrite freshloc_irrefl; intuition.
                econstructor; eauto.
                  econstructor; eauto.
                  intuition. 
         exists EmptyEffect. 
         intuition. right. split. omega.
                exists O. constructor.
          trivial. reflexivity. }
{  (* ifthenelse *) 
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      destruct (EFF_step_case_Ite _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS _ _ _ _ _ _ _ _ _ H H0 MK EQ EQ1 EQ0) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'.
      intuition.
      exists EmptyEffect. intuition. }
{  (* loop *)
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      destruct (EFF_step_case_Loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS _ _ MK EQ) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'.
      intuition.
      exists EmptyEffect. intuition. }
{  (* block *)
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      destruct (EFF_step_case_Block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS _ _ MK EQ) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'.
      intuition.
      exists EmptyEffect. intuition. }
{  (*exit seq*)
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      destruct (EFF_step_case_ExitSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        PRE TRF MCS n  _ MK) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'.
      intuition.
      exists EmptyEffect. intuition. }
{  (*exit block zero*)
      destruct MC as [SMC PRE].
      inv SMC.
      monadInv TR.
      destruct (EFF_step_case_ExitBlockZero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        PRE TRF MCS MK) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'.
      intuition.
      exists EmptyEffect. intuition. }
{  (*exit block nonzero*)
      destruct MC as [SMC PRE].
      inv SMC.
      monadInv TR.
      destruct (EFF_step_case_ExitBlockNonzero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        PRE TRF MCS n MK) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'.
      intuition.
      exists EmptyEffect. intuition. }
{ (*switch*)
      destruct MC as [SMC PRE].
      inv SMC.
      monadInv TR.
      destruct (EFF_step_case_Switch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          PRE TRF MCS _ _ _ _ _ _ MK H EQ EQ0) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'.
      intuition.
      exists EmptyEffect. intuition. }
{ (*return none*) 
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      exploit match_callstack_freelist; try eassumption; try apply PRE.
      intros [tm' [A [B C]]].
      assert (SMV': sm_valid mu m' tm').
        destruct PRE as [? [? [? [SMV _]]]]. 
        split; intros.
          red. rewrite (nextblock_freelist _ _ _ H).
            eapply SMV; assumption.
          apply (Mem.valid_block_free_1 _ _ _ _ _ A).
            eapply SMV; assumption.
      eexists; eexists; exists mu; intuition; simpl.
       Focus 6. assert (VV: Mem.valid_block m2 sp).
                  inv MCS. eapply H3. unfold RNG, DomTgt. rewrite SPlocal. trivial.
                exists (FreeEffect m2 0 (fn_stackspace tfn) sp).
                intuition.
                left. apply effstep_plus_one.
                   eapply cmin_effstep_return_0. eauto.
                apply FreeEffectD in H5. destruct H5 as [? [VB Arith]]; subst. 
                  inv MCS. unfold visTgt. rewrite SPlocal; trivial.
           apply FreeEffectD in H5. destruct H5 as [? [VB Arith]]; subst. 
                  inv MCS. rewrite SPlocal in *. discriminate.
       apply intern_incr_refl.
    apply gsep_refl.
        apply sm_inject_separated_same_sminj.
        apply sm_locally_allocatedChar.
          apply freshloc_free_list in H. 
          apply freshloc_free in A.
          repeat split; try extensionality bb; simpl;
          try rewrite H; try rewrite A; intuition.
       split; simpl.
         eapply SMC_returnstate. apply B.
         eapply match_call_cont; eauto.
         constructor.
         intuition. 
           eapply REACH_closed_freelist; try eassumption. }
{ (*return some*)
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      exploit transl_expr_correct; try eassumption; try eapply PRE.
      intros [tv [EVAL [VINJ APP]]].
      exploit match_callstack_freelist; try eassumption; try eapply PRE.  
      intros [tm' [A [B C]]].
      assert (SMV': sm_valid mu m' tm').
        destruct PRE as [? [? [? [SMV _]]]]. 
        split; intros.
          red. rewrite (nextblock_freelist _ _ _ H0).
            eapply SMV; eassumption.
          apply (Mem.valid_block_free_1 _ _ _ _ _ A).
            eapply SMV; eassumption.
      eexists; eexists; exists mu.
      intuition. 
      Focus 6. assert (VV: Mem.valid_block m2 sp).
                  inv MCS. eapply H4. unfold RNG, DomTgt. rewrite SPlocal. trivial.
          exists (FreeEffect m2 0 (fn_stackspace tfn) sp).
                intuition.
                left. apply effstep_plus_one.
                   eapply cmin_effstep_return_1. eauto. eauto. 
                apply FreeEffectD in H6. destruct H6 as [? [VB Arith]]; subst. 
                  inv MCS. unfold visTgt. rewrite SPlocal; trivial.
           apply FreeEffectD in H6. destruct H6 as [? [VB Arith]]; subst. 
                  inv MCS. rewrite SPlocal in *. discriminate.
        apply intern_incr_refl.
    apply gsep_refl.
        apply sm_inject_separated_same_sminj.
        apply sm_locally_allocatedChar.
          apply freshloc_free_list in H0. 
          apply freshloc_free in A.
          repeat split; try extensionality bb; simpl;
          try rewrite H0; try rewrite A; intuition.
       split; simpl.
         eapply SMC_returnstate. apply B.
         eapply match_call_cont; eauto.
         assumption.
         intuition. 
           eapply REACH_closed_freelist; try eassumption. }
{ (*label*)
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      eexists; eexists; exists mu. 
      intuition.
      Focus 6. exists EmptyEffect. intuition.
               left. eapply effstep_plus_one.
                       constructor.  
      apply intern_incr_refl.
    apply gsep_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
          repeat split; try extensionality bb; simpl;
          try rewrite freshloc_irrefl; intuition.
      econstructor; eauto.
        econstructor; eauto.
        intuition. }
{  (*goto*)
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR.
      exploit transl_find_label_body; try eassumption.  
      intros [ts' [tk' [xenv' [A [B C]]]]].
      eexists; eexists; exists mu. 
      intuition.
      Focus 6. exists EmptyEffect. intuition.
               left. eapply effstep_plus_one.
                       apply cmin_effstep_goto. eexact A. 
      apply intern_incr_refl.
    apply gsep_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
          repeat split; try extensionality bb; simpl;
          try rewrite freshloc_irrefl; intuition.
      econstructor; eauto.
        econstructor; eauto.
        intuition. }
{  (* internal call *) 
      destruct MC as [SMC PRE].
      inv SMC. 
      monadInv TR. 
      exploit EFF_step_case_InternalCall; try eassumption.
      intros IC. destruct IC as [c2' [m2' [mu' XX]]].
      exists c2', m2', mu'. intuition.
      exists EmptyEffect. intuition. }

(* no case for external calls *)

{  (* return *) 
      destruct MC as [SMC PRE].
      inv SMC.
      inv MK. simpl.
      eexists; eexists; exists mu; intuition. 
      Focus 6. exists EmptyEffect. intuition.
               left. eapply effstep_plus_one.
                       econstructor; eauto.   
      apply intern_incr_refl.
    apply gsep_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
          repeat split; try extensionality bb; simpl;
          try rewrite freshloc_irrefl; intuition.
      econstructor; eauto. simpl. inv MCS.
        econstructor; eauto.
        unfold set_optvar. destruct optid; simpl option_map; econstructor; eauto.
        eapply match_temps_assign. assumption. assumption.
      simpl; intuition. }
Qed. 

(*program structure not yet updated to module*)
Theorem transl_program_correct
        (R: list_norepet (map fst (prog_defs prog))):
  SM_simulation.SM_simulation_inject (csharpmin_eff_sem hf) 
   (cmin_eff_sem hf) ge tge.
Proof.
 eapply simulations_lemmas.inj_simulation_star with
  (match_states:=MATCH) (measure:=MC_measure).
(*genvs_dom_eq*)
  apply GDE_lemma.
(*ginfos_preserved*)
  unfold tge, ge. 
  split; red; intros.
   rewrite (varinfo_preserved _ _ TRANSL). apply gvar_info_refl.
   rewrite (symbols_preserved _ _ TRANSL). trivial.
(*match_wd*)
  apply MATCH_sm_wd.
(*match_visible*)
  apply MATCH_visible.
(*match_restrict
  apply MATCH_restrict.*)
(*match_valid*)
  apply MATCH_validblocks.
(*match_genv*)
  apply MATCH_genv.
(*initial_core*)
  intros. eapply Match_init_core; try eassumption.
(*halted*) 
  { intros. destruct H as [MC [RC [PG [GF [VAL [WD INJ]]]]]]. 
    eapply MATCH_safely_halted in MC; eauto.
    destruct MC as [v2 [A B]].
    exists v2. intuition. }
(* at_external*)
  { apply MATCH_atExternal. }
(* after_external*)
  { intros.
    eapply (MATCH_AfterExternal mu st1 st2 m1 e vals1 m2 
             ef_sig vals2 e' ef_sig') with
            (pubSrc':=pubSrc') (pubTgt':=pubTgt') 
            (frgnSrc':=frgnSrc') (frgnTgt':=frgnTgt')
            (nu:=nu) (nu':=nu') (mu':=mu');
     try assumption; try reflexivity. }
(* effcore_diagram*)
  { intros. 
    destruct (MATCH_effcore_diagram _ _ _ _ _ H _ _ _ H0)
      as [st2' [m2' [mu' [INT [SEP [LOCALLOC [MTCH U]]]]]]]. 
    exists st2', m2', mu'.
    split; try eassumption.
    split; try eassumption.
    split; try eassumption. }
Qed.

End TRANSLATION.


