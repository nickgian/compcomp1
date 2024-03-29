Require Import Bool.

Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import semantics.
Require Import effect_semantics.
Require Import structured_injections.
Require Import reach.
Require Export globalSep.


(** * Structured Simulations *)

Definition mem_respects_readonly {F V} (ge : Genv.t F V) m :=
    forall b gv, Genv.find_var_info ge b = Some gv ->
                 gvar_readonly gv && negb (gvar_volatile gv) = true ->
           Genv.load_store_init_data ge m b 0 (gvar_init gv) /\
           Mem.valid_block m b /\ (forall ofs : Z, ~ Mem.perm m b ofs Max Writable).

Lemma mem_respects_readonly_forward {F V} (ge : Genv.t F V) m m'
         (MRR: mem_respects_readonly ge m)
         (FWD: mem_forward m m'): mem_respects_readonly ge m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' [Perm RDO]].
split. specialize (RDO NP). eapply Genv.load_store_init_data_invariant; eassumption.
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

Definition gvar_info_eq {V1 V2} (v1: option (globvar V1)) (v2: option (globvar V2)) :=
  match v1, v2 with
    None, None => True
  | Some i1, Some i2 => gvar_init i1 = gvar_init i2 /\
                        gvar_readonly i1 = gvar_readonly i2 /\ gvar_volatile i1 = gvar_volatile i2
  | _, _ => False
  end. 

Definition gvar_infos_eq {F1 V1 F2 V2} 
  (g1 : Genv.t F1 V1) (g2 : Genv.t F2 V2) :=
  forall b, gvar_info_eq (Genv.find_var_info g1 b) (Genv.find_var_info g2 b).

Lemma gvar_info_refl V v: @gvar_info_eq V V v v. 
  destruct v; simpl; intuition. Qed.

(*
Definition gvar_info_rev {F1 V1 F2 V2} 
  (g1 : Genv.t F1 V1) (g2 : Genv.t F2 V2) :=
  forall b gv',
  Genv.find_var_info g2 b = Some gv' ->
  exists gv,
    Genv.find_var_info g1 b = Some gv /\ gvar_init gv = gvar_init gv' /\ 
    gvar_readonly gv = gvar_readonly gv' /\ gvar_volatile gv = gvar_volatile gv'. 

Definition gvar_info {F1 V1 F2 V2} 
  (g1 : Genv.t F1 V1) (g2 : Genv.t F2 V2) :=
  forall b gv,
  Genv.find_var_info g1 b = Some gv ->
  exists gv',
    Genv.find_var_info g2 b = Some gv' /\ gvar_init gv = gvar_init gv' /\ 
    gvar_readonly gv = gvar_readonly gv' /\ gvar_volatile gv = gvar_volatile gv'. 

Goal forall  {F1 V1 F2 V2} (g1 : Genv.t F1 V1) (g2 : Genv.t F2 V2),
  gvar_infos g1 g2 = (gvar_info g1 g2 /\ gvar_info_rev g1 g2).
Proof. unfold gvar_infos, gvar_info, gvar_info_rev. intros.
  apply prop_ext. split; intros.
  split; intros. unfold gvar_info_eq in H; specialize (H b); simpl in H.
      rewrite H0 in H. destruct (Genv.find_var_info g2 b); try contradiction.
      exists g; intuition. 
    unfold gvar_info_eq in H; specialize (H b); simpl in H.
      rewrite H0 in H. destruct (Genv.find_var_info g1 b); try contradiction.
      exists g; intuition.
  destruct H; red; intros. specialize (H b); specialize (H0 b).
    destruct (Genv.find_var_info g1 b); destruct (Genv.find_var_info g2 b); trivial.

     destruct (H _ (eq_refl _)) as [? [? ?]]; clear H. inv H1.
     destruct (H0 _ (eq_refl _)) as [? [? ?]]; clear H0. inv H. intuition.

     destruct (H _ (eq_refl _)) as [? [? ?]]; clear H. inv H1.

     destruct (H0 _ (eq_refl _)) as [? [? ?]]; clear H0. inv H1.
Qed. 
*)

Definition findsymbols_preserved {F1 V1 F2 V2} (g1 : Genv.t F1 V1) (g2 : Genv.t F2 V2) := 
  forall i b, Genv.find_symbol g1 i = Some b -> Genv.find_symbol g2 i = Some b.

Module SM_simulation. Section SharedMemory_simulation_inject. 

(** Structured simulations are parameterized by a source interaction semantics
    [Sem1] and by a target interaction semantics [Sem2]. *)

(** [ge1] and [ge2] are the global environments associated with [Sem1] and
    [Sem2] respectively. *)

Context 
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

Record SM_simulation_inject := { 
  (** The type of auxiliary data used to model stuttering. *)
  core_data : Type

  (** The (existentially quantified) match-state relation of the simulation. *)
; match_state : core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop

  (** A well-founded order on values of type [core_data]. *)
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord

  (** The match relation implies that [mu] is well-defined. *)
; match_sm_wd : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 -> SM_wd mu

  (** The global environments have equal domain. *)
; genvs_dom_eq : genvs_domain_eq ge1 ge2

  (** The global environments also assocaite same info with global blocks and 
      preserve find_var. These conditions are used for in the transitivity proof,
      to establish mem_respects_readonly for the intermediate memory and globalenv. *)
; ginfo_preserved : gvar_infos_eq ge1 ge2 /\ findsymbols_preserved ge1 ge2

  (** The injection [mu] preserves global blocks. *)
; match_genv : 
    forall d mu c1 m1 c2 m2 (MC : match_state d mu c1 m1 c2 m2),
    meminj_preserves_globals ge1 (extern_of mu) /\
    (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true)

  (** The set of visible blocks is [REACH]-closed. *)
; match_visible : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 -> 
    REACH_closed m1 (vis mu)

  (** [match_state] is closed under restriction to reach-closed supersets of 
      the visible blocks. REMOVED in jan. 2015*)
(*; match_restrict:
    forall d mu c1 m1 c2 m2,
      match_state d mu c1 m1 c2 m2 ->
      forall X, (forall b, vis mu b = true -> X b = true) ->
                REACH_closed m1 X ->
      match_state d (restrict_sm mu X) c1 m1 c2 m2*)


  (** The blocks in the domain/range of [mu] are valid in [m1]/[m2]. *)
; match_validblocks : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 ->
    sm_valid mu m1 m2

  (** The clause that relates initial states. *)
; core_initial : 
    forall v vals1 c1 m1 j vals2 m2 DomS DomT,
    initial_core Sem1 ge1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j ->
    globalfunction_ptr_inject ge1 j -> 

    (*the next two conditions are required to guarantee initialSM_wd*)
    (forall b1 b2 d, j b1 = Some (b2, d) -> 
      DomS b1 = true /\ DomT b2 = true) ->
    (forall b, 
      REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b=true -> 
      DomT b = true) ->

    mem_respects_readonly ge1 m1 -> mem_respects_readonly ge2 m2 ->

    (*the next two conditions ensure the initialSM satisfies sm_valid*)
    (forall b, DomS b = true -> Mem.valid_block m1 b) ->
    (forall b, DomT b = true -> Mem.valid_block m2 b) ->

    exists cd, exists c2, 
    initial_core Sem2 ge2 v vals2 = Some c2 
    /\ match_state cd 
         (initial_SM DomS DomT 
           (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
           (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
         c1 m1 c2 m2

  (** The diagram for internal steps. *)
; effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
      intern_incr mu mu'
      /\ globals_separate ge2 mu mu' 
      /\ sm_locally_allocated mu mu' m1 m2 m1' m2' 
      /\ match_state cd' mu' st1' m1' st2' m2'
      /\ exists U2,              
          ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
            (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
             core_ord cd' cd)) /\
         forall 
           (UHyp: forall b1 z, U1 b1 z = true -> vis mu b1 = true)
           b ofs (Ub: U2 b ofs = true),
           visTgt mu b = true 
           /\ (locBlocksTgt mu b = false ->
               exists b1 delta1, 
                 foreign_of mu b1 = Some(b,delta1) 
                 /\ U1 b1 (ofs-delta1) = true 
                 /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty))

  (** The clause that relates halted states. *)      
; core_halted : 
    forall cd mu c1 m1 c2 m2 v1,
    match_state cd mu c1 m1 c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists v2, 
    Mem.inject (as_inj mu) m1 m2 
    /\ val_inject (restrict (as_inj mu) (vis mu)) v1 v2 
    /\ halted Sem2 c2 = Some v2 

  (** The clause that relates [at_external] call points. *)      
; core_at_external : 
    forall cd mu c1 m1 c2 m2 e vals1 ef_sig,
    match_state cd mu c1 m1 c2 m2 ->
    at_external Sem1 c1 = Some (e,ef_sig,vals1) ->
    Mem.inject (as_inj mu) m1 m2 
    /\ exists vals2, 
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 
       /\ at_external Sem2 c2 = Some (e,ef_sig,vals2)

    /\ forall
       (pubSrc' pubTgt' : block -> bool)
       (pubSrcHyp : pubSrc' =
                  (fun b : block =>
                  locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
       (pubTgtHyp: pubTgt' =
                  (fun b : block =>
                  locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       nu (Hnu: nu = (replace_locals mu pubSrc' pubTgt')),
       match_state cd nu c1 m1 c2 m2 
       /\ Mem.inject (shared_of nu) m1 m2

  (** The diagram for external steps. *)
; eff_after_external: 
    forall cd mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu: Mem.inject (as_inj mu) m1 m2)
      (MatchMu: match_state cd mu st1 m1 st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals1))

        (** We include the clause [AtExtTgt] to ensure that [vals2] is uniquely
         determined. We have [e=e'] and [ef_sig=ef_sig'] by the [at_external]
         clause, but omitting the hypothesis [AtExtTgt] would result in two not
         necesssarily equal target argument lists in language three in the
         transitivity proof, as [val_inject] is not functional in the case in
         which the left value is [Vundef] ([Vundef]s can be refined under memory
         injections to arbitrary values). *)

      (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals2)) 
      (ValInjMu: Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)  

      pubSrc' 
      (pubSrcHyp: 
         pubSrc' 
         = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
        
      pubTgt' 
      (pubTgtHyp: 
         pubTgt' 
         = fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b)

      nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),

      forall nu' ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res (AST.ef_sig e)))
        (HasTy2: Val.has_type ret2 (proj_sig_res (AST.ef_sig e')))
        (INC: extern_incr nu nu') 
        (GSep: globals_separate ge2 nu nu')

        (WDnu': SM_wd nu') (SMvalNu': sm_valid nu' m1' m2')

        (MemInjNu': Mem.inject (as_inj nu') m1' m2')
        (RValInjNu': val_inject (as_inj nu') ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')

        frgnSrc' 
        (frgnSrcHyp: 
           frgnSrc' 
           = fun b => DomSrc nu' b && 
                      (negb (locBlocksSrc nu' b) && 
                       REACH m1' (exportedSrc nu' (ret1::nil)) b))

        frgnTgt' 
        (frgnTgtHyp: 
           frgnTgt' 
           = fun b => DomTgt nu' b &&
                      (negb (locBlocksTgt nu' b) &&
                       REACH m2' (exportedTgt nu' (ret2::nil)) b))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
 
         (UnchPrivSrc: 
            Mem.unchanged_on (fun b ofs => 
              locBlocksSrc nu b = true /\ 
              pubBlocksSrc nu b = false) m1 m1') 

         (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' mu' st1' m1' st2' m2' }.

Require Import semantics_lemmas.

(** Derive an effectless internal step diagram clause from the effectful diagram
  above. *)

Lemma core_diagram (SMI: SM_simulation_inject):
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 mu m2,
        match_state SMI cd mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists mu',
          intern_incr mu mu' /\
          globals_separate ge2 mu mu' /\ 
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 
          match_state SMI cd' mu' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord SMI cd' cd).
Proof. intros. 
apply effax2 in H. destruct H as [U1 H]. 
exploit (effcore_diagram SMI); eauto.
intros [st2' [m2' [cd' [mu' [INC [GSEP [LOCALLOC 
  [MST [U2 [STEP _]]]]]]]]]].
exists st2', m2', cd', mu'.
split; try assumption.
split; try assumption.
split; try assumption.
split; try assumption.
destruct STEP as [[n STEP] | [[n STEP] CO]];
  apply effstepN_corestepN in STEP.
left. exists n. assumption.
right; split; trivial. exists n. assumption.
Qed.

End SharedMemory_simulation_inject. 

End SM_simulation.

