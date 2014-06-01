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
Require Import core_semantics.
Require Import core_semantics_lemmas.
Require Import StructuredInjections.
 
Record EffectSem {G C} :=
  { sem :> CoopCoreSem G C;

    effstep: G -> (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop;

    effax1: forall M g c m c' m',
       effstep g M c m c' m' ->
            corestep sem g c m c' m'  
         /\ Mem.unchanged_on (fun b ofs => M b ofs = false) m m';

    effax2: forall g c m c' m',
       corestep sem g c m c' m' ->
       exists M, effstep g M c m c' m';

    effstep_valid: forall M g c m c' m',
       effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b
  }.

(** This module defines an effect semantics typeclass, for building 
    functors over effsem-like objects.  *)

Module Effsem.
Class t {G C : Type} : Type :=
  { sem :> CoopCoreSem G C;
    effstep: G -> (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop;
    effax1: forall M g c m c' m',
       effstep g M c m c' m' ->
            corestep sem g c m c' m'  
         /\ Mem.unchanged_on (fun b ofs => M b ofs = false) m m';
    effax2: forall g c m c' m',
       corestep sem g c m c' m' ->
       exists M, effstep g M c m c' m';
    effstep_valid: forall M g c m c' m',
       effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b }.
End Effsem.

Instance effsem_instance (G C : Type) (sem : @EffectSem G C) : @Effsem.t G C :=
  Effsem.Build_t G C  
    sem
    (effstep sem)
    (effax1 sem) 
    (effax2 sem)
    (effstep_valid sem).

Definition effstep_fun {G C : Type} (sem : @EffectSem G C) :=
  forall (m m' m'' : mem) ge c c' c'' U U',
  effstep sem ge U c m c' m' -> 
  effstep sem ge U' c m c'' m'' -> 
  U=U' /\ c'=c'' /\ m'=m''.

Section effsemlemmas.
  Context {G C:Type} (Sem: @EffectSem G C) (g:G).

  Lemma effstep_corestep: forall M g c m c' m',
      effstep Sem g M c m c' m' -> corestep Sem g c m c' m'. 
  Proof. intros. apply effax1 in H. apply H. Qed.

  Lemma effstep_unchanged: forall M g c m c' m',
        effstep Sem g M c m c' m' -> 
        Mem.unchanged_on (fun b ofs => M b ofs = false) m m'.
  Proof. intros. apply effax1 in H. apply H. Qed.

  Lemma effstep_fwd: forall U c m c' m',
    effstep Sem g U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct Sem.
         eapply corestep_fwd. eapply effax1. apply H.
  Qed.

  Fixpoint effstepN (n:nat) : (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop :=
    match n with
      | O => fun U c m c' m' => (c,m) = (c',m') /\ U = (fun b z => false)
      | S k => fun U c1 m1 c3 m3 => exists c2, exists m2, exists U1, exists U2,
        effstep Sem g U1 c1 m1 c2 m2 /\
        effstepN k U2 c2 m2 c3 m3 /\ 
        U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b))
    end.

Lemma effstepN_valid: forall n U c1 m1 c2 m2, effstepN n U c1 m1 c2 m2 ->
       forall b z, U b z = true -> Mem.valid_block m1 b.
Proof. intros n.
  induction n; simpl; intros. destruct H; subst. discriminate.
  destruct H as [c [m [U1 [U2 [Step [StepN UU]]]]]]; subst; simpl.
  specialize (IHn _ _ _ _ _ StepN). 
  specialize (effstep_valid _ _ _ _ _ _ _ Step b z). intros.
  remember (U1 b z) as d.
  destruct d; simpl in *. apply H; trivial.
  destruct (valid_block_dec m1 b). trivial. simpl in *.
  rewrite andb_false_r in H0. inv H0.
Qed.

  Lemma effstepN_fwd: forall n U c m c' m',
    effstepN n U c m c' m' -> mem_forward m m'.
  Proof. intros n.
         induction n; intros; simpl in *. destruct H.
           inv H. eapply mem_forward_refl.
         destruct H as [c1 [c2 [Eff1 [Eff2 [Step1 [Step2 HU]]]]]].
         eapply mem_forward_trans.
           eapply effstep_fwd; eassumption.
           eapply IHn; eassumption. 
  Qed.

  Lemma effstepN_corestepN: forall n E c m c' m',
      effstepN n E c m c' m' -> corestepN Sem g n c m c' m'. 
  Proof. intros n.
    induction n; intros; simpl in *.
        apply H. 
      destruct H as [c1 [m1 [U1 [U2 [Estep [EN HE]]]]]].
        apply effstep_corestep in Estep.
        apply IHn in EN. exists c1, m1.
        split; eassumption.
  Qed.

  Lemma effstepN_unchanged: forall n U c1 m1 c2 m2,
        effstepN n U c1 m1 c2 m2 -> 
        Mem.unchanged_on (fun b z => U b z = false) m1 m2.
  Proof. intros n.
    induction n; simpl; intros.
      destruct H. inv H. apply Mem.unchanged_on_refl.
    rename c2 into c3. rename m2 into m3.
    destruct H as [c2 [m2 [E1 [E2 [Step1 [Step2 HE]]]]]].
    apply IHn in Step2; clear IHn. subst.
    assert (FWD:= effstep_fwd _ _ _ _ _ Step1).
    apply effstep_unchanged in Step1.
    split; intros.
     apply orb_false_iff in H. destruct H.
     remember (valid_block_dec m1 b) as v.
     destruct v; simpl in *; try contradiction.
     clear H0 Heqv.
     rewrite andb_true_r in H1.     
     split; intros. apply Step2; trivial.
        apply (FWD _ v). 
     apply Step1; try assumption.

     apply Step1; try assumption.
       apply Step2; try assumption. 
        apply (FWD _ v).

   apply orb_false_iff in H. destruct H.
     remember (valid_block_dec m1 b) as v.
     destruct v; simpl in *; try contradiction.
     clear Heqv.
     rewrite andb_true_r in H1.
     destruct Step2. rewrite unchanged_on_contents; trivial.
       eapply Step1; try eassumption.
       eapply Step1; try eassumption.
     elim n0. eapply Mem.perm_valid_block; eassumption.
  Qed.

Lemma effstepN_trans: forall n1 n2 U1 st1 m1 st2 m2 U2 st3 m3,
      effstepN n1 U1 st1 m1 st2 m2 ->
      effstepN n2 U2 st2 m2 st3 m3 ->
   effstepN (n1+n2)
        (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) st1 m1 st3 m3.
Proof. intros n1.
induction n1; simpl.
  intros. destruct H; subst. inv H. simpl.
  assert (U2 = (fun b z => U2 b z && valid_block_dec m2 b)).
    extensionality b; extensionality z.
    remember (U2 b z) as d. destruct d; trivial.
    apply eq_sym in Heqd.
    apply (effstepN_valid _ _ _ _ _ _ H0) in Heqd.
    remember (valid_block_dec m2 b) as q.
    destruct q; trivial. contradiction.
  rewrite H in H0. apply H0.
intros. rename st3 into st4. rename m3 into m4.
   rename st2 into st3. rename m2 into m3.
   rename U1 into U. rename U2 into U3.
   destruct H as [st2 [m2 [U1 [U2 [Step1 [Step2 HU]]]]]].
   subst; simpl in *.
   exists st2, m2, U1; simpl.
   specialize (IHn1 _ _ _ _ _ _ _ _ _ Step2 H0). 
   clear Step2 H0.
   eexists; split. assumption.
   split. eassumption.
   extensionality b; extensionality z; simpl.
   remember (U1 b z) as d. destruct d; simpl; trivial; apply eq_sym in Heqd.
   remember (U2 b z) as q. destruct q; simpl; trivial; apply eq_sym in Heqq.
     remember (valid_block_dec m1 b) as u.
     destruct u; trivial; simpl. apply andb_false_r.
   remember (U3 b z) as p. destruct p; simpl; trivial; apply eq_sym in Heqp.
     remember (valid_block_dec m1 b) as u.
     destruct u; trivial; simpl. clear Hequ. rewrite andb_true_r.
       apply effstep_fwd in Step1. apply Step1 in v.
       destruct (valid_block_dec m2 b); trivial. destruct v; contradiction.
     rewrite andb_false_r. trivial.
Qed.

Lemma effstepN_trans': forall n1 n2 U U1 st1 m1 st2 m2 U2 st3 m3,
      effstepN n1 U1 st1 m1 st2 m2 ->
      effstepN n2 U2 st2 m2 st3 m3 ->
      U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
   effstepN (n1+n2) U st1 m1 st3 m3.
Proof. intros; subst. eapply effstepN_trans; eassumption. Qed.

  Definition effstep_plus U c m c' m' :=
    exists n, effstepN (S n) U c m c' m'.

  Definition effstep_star U c m c' m' :=
    exists n, effstepN n U c m c' m'.

  Lemma effstep_plus_star : forall U c1 c2 m1 m2,
    effstep_plus U c1 m1 c2 m2 -> effstep_star U c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma effstep_plus_trans : forall U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 -> 
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + (S n2))%nat). simpl.
    apply (effstepN_trans (S n1) (S n2) U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma effstep_plus_trans' : forall U U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 -> 
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_plus_trans; eassumption. Qed.

  Lemma effstep_star_plus_trans : forall U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_star U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 -> 
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + n2)%nat).
    specialize (effstepN_trans n1 (S n2) U1 c1 m1 c2 m2 U2 c3 m3 H1 H2); intros H.
    rewrite <- plus_n_Sm in H. assumption.
  Qed.
  Lemma effstep_star_plus_trans' : forall U U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_star U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 -> 
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_star_plus_trans; eassumption. Qed. 

  Lemma effstep_plus_star_trans: forall U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 -> 
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + n2)%nat).
    apply (effstepN_trans _ _  U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma effstep_plus_star_trans': forall U U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 -> 
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_plus_star_trans; eassumption. Qed. 

  Lemma effstep_star_trans: forall U1 c1 c2 c3 U2 m1 m2 m3, 
    effstep_star U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 -> 
    effstep_star (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    eexists.
    eapply (effstepN_trans _ _ U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma effstep_star_trans': forall U U1 c1 c2 c3 U2 m1 m2 m3, 
    effstep_star U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 -> 
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_star U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_star_trans; eassumption. Qed. 

  Lemma effstep_plus_one: forall U c m c' m',
    effstep Sem g U c m c' m' -> effstep_plus U c m c' m'.
  Proof. intros. exists O. simpl. exists c', m', U, (fun b z =>false).
    intuition.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma effstep_plus_two: forall U1 c m c' m' U2 c'' m'',
    effstep  Sem g U1 c m c' m' -> effstep Sem g U2 c' m' c'' m'' -> 
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m b)) c m c'' m''.
  Proof. intros. 
    exists (S O). exists c', m', U1, U2. split; trivial.
    split; trivial. simpl. 
    exists c'', m'', U2, (fun b z =>false).
    intuition.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma effstep_star_zero: forall c m, effstep_star (fun b z =>false) c m c m.
  Proof. intros. exists O. simpl. split; reflexivity. Qed.

  Lemma effstep_star_one: forall U c m c' m',
    effstep  Sem g U c m c' m' -> effstep_star U c m c' m'.
  Proof. intros. 
    exists (S O). exists c', m', U, (fun b z =>false).
    simpl; split; trivial. split. split; reflexivity.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.     
  Qed.

  Lemma effstep_plus_split: forall U c m c' m',
    effstep_plus U c m c' m' ->
    exists c'', exists m'', exists U1, exists U2,
      effstep Sem g U1 c m c'' m'' /\ 
      effstep_star U2 c'' m'' c' m' /\
      U = (fun b z => U1 b z || (U2 b z && valid_block_dec m b)).
  Proof. intros.
    destruct H as [n [c2 [m2 [U1 [U2 [Hstep [Hstar HU]]]]]]].
    exists c2, m2, U1, U2. split. assumption. split; try assumption.
    exists n. assumption. 
  Qed.

  Lemma effstep_star_fwd: forall U c m c' m',
    effstep_star U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct H as [n H]. 
      eapply effstepN_fwd; eassumption.
  Qed.

  Lemma effstep_plus_fwd: forall U c m c' m',
    effstep_plus U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct H as [n H]. 
      eapply effstepN_fwd; eassumption.
  Qed.

End effsemlemmas.


Definition EmptyEffect: Values.block -> Z -> bool := fun b z => false.

Lemma EmptyEffect_alloc: forall m lo hi m' b (ALLOC: Mem.alloc m lo hi = (m', b)),
      Mem.unchanged_on (fun b ofs => EmptyEffect b ofs = false) m m'.
Proof. intros.
       eapply Mem.alloc_unchanged_on; eassumption.
Qed. 

Definition FreeEffect m lo hi (sp b:Values.block) (ofs:Z): bool := 
   if valid_block_dec m b 
   then eq_block b sp && zle lo ofs && zlt ofs hi
   else false.

Lemma FreeEffectD: forall m lo hi sp b z 
   (FREE:FreeEffect m lo hi sp b z = true),
   b = sp /\ Mem.valid_block m b /\ lo <= z /\ z < hi.
Proof. intros.
  unfold FreeEffect in FREE.
  destruct (valid_block_dec m b); simpl in *; try discriminate.
  destruct (eq_block b sp); subst; simpl in *; try discriminate.
  destruct (zle lo z); simpl in *; try discriminate.
  destruct (zlt z hi); simpl in *; try discriminate.
  auto.
Qed.

Lemma FreeEffect_free: forall m sp lo hi m'
             (FREE: Mem.free m sp lo hi = Some m'),
     Mem.unchanged_on  (fun b ofs => FreeEffect m lo hi sp b ofs = false) m m'.
Proof. intros.
       eapply Mem.free_unchanged_on; try eassumption.
               intros. unfold FreeEffect; simpl. intros N.
               destruct (valid_block_dec m sp).
               apply andb_false_iff in N. destruct H.
               destruct (eq_block sp sp); simpl in *.
                 destruct N. destruct (zle lo i). inv H1. xomega.
               destruct (zlt i hi). inv H1. xomega.
               apply n; trivial.
               apply Mem.free_range_perm in FREE.
                 apply n; clear n.
                 eapply Mem.perm_valid_block.
                 eapply (FREE lo). omega.
Qed. 

Definition FreelistEffect 
  m (L: list (Values.block * Z * Z)) (b:Values.block) (ofs:Z): bool := 
  List.fold_right (fun X E b z => match X with (bb,lo,hi) =>
                                   E b z || FreeEffect m lo hi bb b z
                                 end) 
                  EmptyEffect L b ofs.

Lemma FreelistEffect_Dfalse: forall m bb lo hi L b ofs
      (F:FreelistEffect m ((bb, lo, hi) :: L) b ofs = false),
      FreelistEffect m L b ofs = false /\
      FreeEffect m lo hi bb b ofs = false. 
Proof. intros.
  unfold FreelistEffect in F. simpl in F.
  apply orb_false_iff in F. apply F.
Qed. 

Lemma FreelistEffect_Dtrue: forall m bb lo hi L b ofs
      (F:FreelistEffect m ((bb, lo, hi) :: L) b ofs = true),
      FreelistEffect m L b ofs = true \/
      FreeEffect m lo hi bb b ofs = true.
Proof. intros.
  unfold FreelistEffect in F. simpl in F.
  apply orb_true_iff in F. apply F.
Qed. 

Lemma FreelistEffect_same: forall m bb lo hi mm L
          (F:Mem.free m bb lo hi = Some mm)
          b (VB: Mem.valid_block mm b) ofs,
      FreelistEffect mm L b ofs = false <-> FreelistEffect m L b ofs = false.
Proof. intros  m bb lo hi mm L.
  induction L; simpl; intros. intuition.
  intuition. 
    apply orb_false_iff in H0. destruct H0.
    specialize (H _ VB ofs).
    apply H in H0. rewrite H0. simpl. clear H H0.
    unfold FreeEffect in *; simpl in *.
    apply Mem.nextblock_free in F. 
    destruct (valid_block_dec m b). 
      destruct (valid_block_dec mm b); trivial.
      red in v. rewrite <- F in v. elim n. apply v.
    trivial.
  apply orb_false_iff in H0. destruct H0.
    specialize (H _ VB ofs).
    apply H in H0. rewrite H0. simpl. clear H H0.
    unfold FreeEffect in *; simpl in *.
    apply Mem.nextblock_free in F. 
    destruct (valid_block_dec mm b). 
      destruct (valid_block_dec m b); trivial.
      red in v. rewrite F in v. elim n. apply v.
    trivial.
Qed.

Lemma FreelistEffect_freelist: forall L m m' (FL: Mem.free_list m L = Some m'),
      Mem.unchanged_on (fun b ofs => FreelistEffect m L b ofs = false) m m'.
Proof. intros L.
  induction L; simpl; intros.
    inv FL. apply Mem.unchanged_on_refl.
  destruct a as [[bb lo] hi].
    remember (Mem.free m bb lo hi) as d.
    destruct d; try inv FL. apply eq_sym in Heqd.
    specialize (IHL _ _ H0).
    assert (FF:= FreeEffect_free _ _ _ _ _ Heqd). 
    eapply (unchanged_on_trans _ m0 _). 
      eapply mem_unchanged_on_sub; try eassumption.
        intuition. apply orb_false_iff in H. apply H.
      clear FF.
      specialize (unchanged_on_validblock_invariant m0 m' 
           (fun (b : block) (ofs : Z) => FreelistEffect m0 L b ofs = false) 
           (fun (b : block) (ofs : Z) => FreelistEffect m L b ofs = false)).
      intros. apply H in IHL. clear H.
        eapply mem_unchanged_on_sub; try eassumption.
        intuition. apply orb_false_iff in H. apply H.
      clear IHL H. intros.
       eapply FreelistEffect_same; eassumption.
   eapply free_forward; eassumption.
Qed.

Lemma FreeEffect_validblock: forall m lo hi sp b ofs
        (EFF: FreeEffect m lo hi sp b ofs = true),
      Mem.valid_block m b.
Proof. intros.
  unfold FreeEffect in EFF.
  destruct (valid_block_dec m b); trivial; inv EFF.
Qed.

Lemma FreelistEffect_validblock: forall l m b ofs
        (EFF: FreelistEffect m l b ofs = true),
      Mem.valid_block m b.
Proof. intros l.
  induction l; unfold FreelistEffect; simpl; intros.
     unfold EmptyEffect in EFF. inv EFF.
  destruct a as [[bb lo] hi].
  apply orb_true_iff in EFF.
  destruct EFF.
  apply IHl in H. assumption.
  eapply FreeEffect_validblock; eassumption.
Qed.

Definition StoreEffect (tv:val)(vl : list memval) (b:Values.block) (z:Z):bool := 
  match tv with Vptr bb ofs => eq_block bb b && 
             zle (Int.unsigned ofs) z && zlt z (Int.unsigned ofs + Z.of_nat (length vl))
         | _ => false
  end.

Lemma StoreEffect_Storev: forall m chunk tv tv' m' 
         (STORE : Mem.storev chunk m tv tv' = Some m'),
      Mem.unchanged_on 
        (fun b ofs => StoreEffect tv (encode_val chunk tv') b ofs = false) 
        m m'.
Proof. intros.
  destruct tv; inv STORE.
  unfold StoreEffect.
  split; intros.
      split; intros. eapply Mem.perm_store_1; eassumption.
      eapply Mem.perm_store_2; eassumption.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ H0). clear H0.
  destruct (eq_block b b0); subst; simpl in *.
    rewrite PMap.gss. apply andb_false_iff in H.  
    apply Mem.setN_outside.
    destruct H. destruct (zle (Int.unsigned i) ofs ); simpl in *. inv H.
                left. xomega.
    right. remember (Z.of_nat (length (encode_val chunk tv'))).
       destruct (zlt ofs (Int.unsigned i + z)); simpl in *. inv H. apply g.
  rewrite PMap.gso. trivial. intros N; subst. elim n; trivial. 
Qed.

Lemma StoreEffectD: forall vaddr v b ofs
      (STE: StoreEffect vaddr v b ofs = true),
      exists i, vaddr = Vptr b i /\
        (Int.unsigned i) <= ofs < (Int.unsigned i + Z.of_nat (length v)).
Proof. intros.
  unfold StoreEffect in STE. destruct vaddr; inv STE.
  destruct (eq_block b0 b); inv H0.
  exists i.
  destruct (zle (Int.unsigned i) ofs); inv H1.
  destruct (zlt ofs (Int.unsigned i + Z.of_nat (length v))); inv H0.
  intuition.
Qed.
       
