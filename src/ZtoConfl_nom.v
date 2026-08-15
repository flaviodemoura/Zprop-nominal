(* begin hide *)
Require Import Metalib.Metatheory.
Require Import Metalib.LibDefaultSimp.
Require Import Metalib.LibLNgen. 

Require Import infra_nom.
Require Import aeq_equiv_es.

(* end hide *)

Inductive refltrans (R: Rel n_sexp) : Rel n_sexp :=
| refl: forall t1 t2, t1 =α t2 -> refltrans R t1 t2
| rtrans: forall t1 t2 t3, R t1 t2 -> refltrans R t2 t3 -> refltrans R t1 t3
| rtrans_aeq: forall t1 t2 t3, t1 =α t2 -> refltrans R t2 t3 -> refltrans R t1 t3.
(* begin hide *)
Lemma refltrans_refl {R: Rel n_sexp}: forall t, refltrans R t t.
Proof.
  intro t. apply refl. apply aeq_refl.
Qed.  
  
Lemma refltrans_composition {R: Rel n_sexp}: forall t1 t2 t3, refltrans R t1 t2 -> refltrans R t2 t3 -> refltrans R t1 t3.
Proof.
  intros t1 t2 t3 H1 H2. generalize dependent t3. induction H1.
  - intros t3 H'. apply rtrans_aeq with t2; assumption.
  - intros t' H'. apply rtrans with t2.
    + assumption.
    + apply IHrefltrans. assumption.
  - intros t' H'. apply rtrans_aeq with t2.
    + assumption.
    + apply IHrefltrans. assumption.
Qed.

Lemma refltrans_n_app_left {R: Rel n_sexp}: forall t1 t1' t2, (refltrans (ctx R) t1 t1') -> refltrans (ctx R) (n_app t1 t2) (n_app t1' t2).
Proof.
  induction 1.
  - apply refl. apply aeq_app.
    + assumption.
    + apply aeq_refl.
  - apply rtrans with (n_app t0 t2).
    + apply step_n_app_left. assumption.
    + apply IHrefltrans.
  - apply rtrans_aeq with (n_app t0 t2).
    + apply aeq_app.
      * assumption.
      * apply aeq_refl.
    + apply IHrefltrans.
Qed.

Lemma refltrans_n_app_right {R: Rel n_sexp}: forall t1 t2 t2', refltrans (ctx R) t2 t2' -> refltrans (ctx R) (n_app t1 t2) (n_app t1 t2').
Proof.
  induction 1.
  - apply refl. apply aeq_app.
    + apply aeq_refl.
    + assumption.
  - apply rtrans with (n_app t1 t2).
    + apply step_n_app_right. assumption.
    + apply IHrefltrans.
  - apply rtrans_aeq with (n_app t1 t2).
    + apply aeq_app.
      * apply aeq_refl.
      * assumption.
    + apply IHrefltrans.
Qed.

Lemma refltrans_n_app (R: Rel n_sexp): forall t1 t2 t3 t4, refltrans (ctx R) t1 t2 -> refltrans (ctx R) t3 t4 -> refltrans (ctx R) (n_app t1 t3) (n_app t2 t4).
Proof.
  intros. apply refltrans_composition with (n_app t2 t3).
    - apply refltrans_n_app_left. assumption.
    - apply refltrans_n_app_right. assumption.
Qed.

Lemma refltrans_n_abs {R: Rel n_sexp}: forall t t' x, refltrans (ctx R) t t' -> refltrans (ctx R) (n_abs x t) (n_abs x t').
Proof.
  induction 1.
  - apply refl. apply aeq_abs_same. assumption.
  - apply rtrans with (n_abs x t2).
    + apply step_n_abs. assumption.
    + apply IHrefltrans.
  - apply rtrans_aeq with (n_abs x t2).
    + apply aeq_abs_same. assumption.
    + apply IHrefltrans.
Qed.

Lemma refltrans_n_abs_diff {R: Rel n_sexp}: forall t1 t2 x y, x <> y -> x `notin` fv_nom t2 -> refltrans (ctx R) t1 (swap x y t2) -> refltrans (ctx R) (n_abs x t1) (n_abs y t2).
Proof.
  intros. inversion H1;subst.
    - apply refl. apply aeq_abs_diff.
      + assumption.
      + assumption.
      + rewrite swap_symmetric. assumption.
    - apply rtrans with (n_abs x t3).
      + apply step_n_abs. assumption.
      + apply refltrans_composition with (n_abs x (swap x y t2)).
        * apply refltrans_n_abs. assumption.
        * apply refl. apply aeq_abs_diff.
          ** assumption.
          ** assumption.
          ** rewrite swap_symmetric. apply aeq_refl.
    - apply refltrans_composition with (n_abs x (swap x y t2)).
      + apply refltrans_n_abs.  assumption.
      + apply refl. apply aeq_abs_diff.
        * assumption.
        * assumption.
        * rewrite swap_symmetric. apply aeq_refl.
Qed.

Lemma refltrans_n_sub_in (R: Rel n_sexp): forall t1 t2 t3 x, refltrans (ctx R) t2 t3 -> refltrans (ctx R) ([x := t2] t1) ([x := t3] t1).
Proof.
  intros t1 t2 t3 x H. induction H.
  - apply refl. apply aeq_sub_same.
    + apply aeq_refl.
    + assumption.
  - apply rtrans with ([x := t2] t1).
    + apply step_n_sub_in. assumption.
    + assumption.
  - apply refltrans_composition with ([x := t2] t1).
    + apply refl. apply aeq_sub_same.
      * apply aeq_refl.
      * assumption.
    + assumption.
Qed.
 
Lemma refltrans_n_sub_out (R: Rel n_sexp): forall t1 t2 t3 x, refltrans (ctx R) t2 t3 -> refltrans (ctx R) ([x := t1] t2) ([x := t1] t3).
Proof.
  intros t1 t2 t3 x H. induction H.
  - apply refl. apply aeq_sub_same.
    + assumption.
    + apply aeq_refl.
  - apply rtrans with ([x := t1] t2).
    + apply step_n_sub_out. assumption.
    + assumption.
  - apply refltrans_composition with ([x := t1] t2).
    + apply refl. apply aeq_sub_same.
      * assumption.
      * apply aeq_refl.
    + assumption.
Qed.
 
Lemma refltrans_n_sub (R: Rel n_sexp): forall t1 t2 t3 t4 x, refltrans (ctx R) t1 t3 -> refltrans (ctx R) t2 t4 -> refltrans (ctx R) (n_sub t1 x t2) (n_sub t3 x t4).
Proof.
  intros. apply refltrans_composition with (n_sub t3 x t2).
  - apply refltrans_n_sub_out. assumption.
  - apply refltrans_n_sub_in. assumption.
Qed.


(** * Compositional Z property modulo implies Confluence *)
(**

In this section, we instantiate the set $A$ of the generic formalization in %\cite{fmm2021}% with [n_sexp]. In addition, some definitions need to be adjusted to deal correctly with $\alpha$-equivalence. The definition of confluence, named [Confl] below is depicted by the following diagram:

    $\centerline{\xymatrix{ & t_1 \ar@{->>}[dl] \ar@{->>}[dr] & \\ t_2
    \ar@{.>>}[dr] & & t_3 \ar@{.>>}[dl] \\ & t_4 & }}$


*)

Definition Confl (R: Rel n_sexp) := forall t1 t2 t3, (refltrans R) t1 t2 -> (refltrans R) t1 t3 -> (exists t4, (refltrans R) t2 t4 /\ (refltrans R) t3 t4).

(**

The goal of this section is to show how confluence can be obtained for an arbitrary binary relation $R$ over [n_sexp] expressions modulo $\alpha$-equivalence. The technique used to prove confluence is known as the _Z Property_ %\cite{vanoostrom:LIPIcs.FSCD.2021.24}%. A function [f: n_sexp -> n_sexp] has the Z property for the binary relation [R] if the following diagram holds:

  $\centerline{\xymatrix{ t_1 \ar[r]_R & t_2 \ar@{.>>}[dl]^R\\ f t_1 \ar@{.>>}[r]_R & f t_2}}$

 *)

Definition f_is_Z (R: Rel n_sexp) (f: n_sexp -> n_sexp) := forall t1 t2, R t1 t2 -> ((refltrans R)  t2 (f t1) /\ (refltrans R) (f t1) (f t2)).

(**

A binary relation [R] has the Z property if there exists a function [f] that has the Z property for [R].

*)

Definition Z_prop (R: Rel n_sexp) := exists f, (f_is_Z R f).

(*
Theorem Z_prop_implies_Confl: forall R, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. unfold Z_prop, Confl in *. intros t1 t2 t3 Hrefl1 Hrefl2. destruct HZ_prop as [g HZ_prop]. generalize dependent t3. induction Hrefl1 as [t1 t2 Haeq' | t1 t1' t2 HR Hrefl1' | t1 t1' t2 Haeq' Hrefl1']. 
  - intros t3 Hrefl2. exists t3; split.
    +  apply refltrans_composition with t1.
       * apply refl. apply aeq_sym. assumption.
       * assumption.
    + apply refl. apply aeq_refl. 
  - intros t3 Hrefl2. 
    assert (Hg1: refltrans R t1' (g t1)).
    { apply HZ_prop; assumption.  } 
    assert (Hg2: refltrans R t1 (g t1)).
    { apply rtrans with t1'; assumption.  }
    apply HZ_prop in HR. destruct HR as [HR' HR]. clear HR. generalize dependent t1'. induction Hrefl2 as [t1 t3 Haeq' | t1 t1'' t3 HR Hrefl2' | t1 t1'' t3 Haeq' Hrefl2'].  
    + intros t1' HR Hrefl1 IHHrefl1 Hg1. apply IHHrefl1 in Hg1. destruct Hg1 as [x Hg1]. exists x. split.
      * apply Hg1.
      * apply refltrans_composition with t1.
        ** apply refl. apply aeq_sym. assumption.
        ** apply refltrans_composition with (g t1).
           *** assumption.
           *** apply Hg1.
    + intros t1' HR' Hrefl1 IHHrefl1 Hg1. apply IHHrefl1 in Hg1. destruct Hg1 as [x Hg1]. apply IHHrefl2' with t1'.
      * apply refltrans_composition with (g t1); apply HZ_prop; assumption.
      * apply HZ_prop in HR. apply refltrans_composition with (g t1).
        ** assumption.
        ** apply HR.
      * assumption.
      * apply IHHrefl1.
      * apply HZ_prop in HR. apply refltrans_composition with (g t1).
        ** assumption.
        ** apply HR.
    + intros t1' HR Hrefl1 IHHrefl1 Hg1. Abort.
*)
  

Definition Z_prop_aeq (R: Rel n_sexp) := exists f, (f_is_Z R f) /\ (forall t1 t2, t1 =α t2 -> f t1 =α f t2).

(** ** Z property modulo implies Confluence *)
Theorem Z_prop_aeq_implies_Confl: forall R, Z_prop_aeq R -> Confl R.
Proof.
  intros R HZ_prop. unfold Z_prop_aeq, Confl in *. intros t1 t2 t3 Hrefl1 Hrefl2. destruct HZ_prop as [f HZ_prop]. destruct HZ_prop as [Z_prop Haeq]. unfold f_is_Z in Z_prop. generalize dependent t3. induction Hrefl1 as [t1 t2 Haeq' | t1 t1' t2 HR Hrefl1' | t1 t1' t2 Haeq' Hrefl1'].
  - intros t3 Hrefl2. exists t3. split.
    + apply aeq_sym in Haeq'. apply refltrans_composition with t1.
      * apply refl. assumption.
      * assumption.
    + apply refl. apply aeq_refl.
  - intros t3 Hrefl2. assert (HR' := HR). apply Z_prop in HR.
    assert (Ht1: refltrans R t1 (f t1)).
    {
      apply rtrans with t1'.
      - assumption.
      - apply HR.
    }
    destruct HR as [Ht1' HR]. clear HR' HR. generalize dependent  t1'.
    induction Hrefl2 as [t1 t3 Haeq' | t1 t1'' t3 HR Hrefl2' | t1 t1'' t3 Haeq' Hrefl2'].
    + intros t1' Ht1' Hrefl1' IHHrefl1'. apply IHHrefl1' in Ht1'. destruct Ht1' as [t4' [IH1 IH1']]. exists t4'. split.
      * assumption.
      * apply refltrans_composition with (f t1).
        ** apply refltrans_composition with t1.
           *** apply refl. apply aeq_sym. assumption.
           *** assumption.
        ** assumption.
    + intros t1' Ht1' Hrefl1' IHHrefl1'. assert (Ht1'' := Ht1'). apply IHHrefl1' in Ht1'. destruct Ht1' as [t4' [IH1 IH1']].
      assert (Hft1'': refltrans R t1' (f t1'')).
      {
        apply Z_prop in HR. apply refltrans_composition with (f t1).
        - assumption.
        - apply HR.
      }
      apply Z_prop in HR. destruct HR as [HR HR'].
      apply IHHrefl2' in Hft1''.
      * assumption.
      * apply refltrans_composition with (f t1); assumption.
      * assumption.
      * apply IHHrefl1'.
    + intros t1' Ht1' Hrefl1' IHHrefl1'.
      assert (Ht1'': refltrans R t1' (f t1'')).
      {
        apply refltrans_composition with (f t1).
        - assumption.
        - apply refl. apply Haeq. assumption.
      }
      assert (Ht1''': refltrans R t1'' (f t1'')).
      {
        apply refltrans_composition with (f t1).
        - apply refltrans_composition with t1.
          + apply refl. apply aeq_sym. assumption.
          + assumption.
        - apply refl. apply Haeq. assumption.
      }
      apply IHHrefl2' with t1'.
      * apply Ht1'''.
      * assumption.
      * assumption.
      * apply IHHrefl1'.
  - intros t3 Hrefl2.
    assert (Hrefl2': refltrans R t1' t3).
    {
      apply refltrans_composition with t1.
      - apply refl. apply aeq_sym. assumption.
      - assumption.
    }
    apply IHHrefl1'. assumption.
Qed.

(** ** Z compositional modulo  *)
Definition f_is_weak_Z (R R': Rel n_sexp) (f: n_sexp -> n_sexp) := forall t1 t2, R t1 t2 -> ((refltrans R') t2 (f t1) /\ (refltrans R') (f t1) (f t2)).
(* begin hide *)
Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

Inductive union {A} (red1 red2: Rel A) : Rel A :=
| union_left: forall t1 t2, red1 t1 t2 -> union red1 red2 t1 t2
| union_right: forall t1 t2, red2 t1 t2 -> union red1 red2 t1 t2.
Notation "R1 !_! R2" := (union R1 R2) (at level 40).

Lemma union_or {A}: forall (r1 r2: Rel A) (t1 t2: A), (r1 !_! r2) t1 t2 <-> (r1 t1 t2) \/ (r2 t1 t2).
Proof.
  intros r1 r2 t1 t2; split.
  - intro Hunion.
    inversion Hunion; subst.
    + left; assumption.
    + right; assumption.
  - intro Hunion.
    inversion Hunion.
    + apply union_left; assumption.
    + apply union_right; assumption.
Qed.

Lemma equiv_refltrans: forall (R R1 R2: Rel n_sexp), (forall t1 t2, R t1 t2 <-> (R1 !_! R2) t1 t2) -> forall t1 t2, refltrans (R1 !_! R2) t1 t2 -> refltrans R t1 t2.
Proof.
  intros R R1 R2 H1 t1 t2 H2. induction H2.
  - apply refl. assumption.
  - apply rtrans with t2.
    + apply H1. assumption.
    + assumption.
  - apply rtrans_aeq with t2; assumption.
  Qed.

Lemma refltrans_union: forall (R R' :Rel n_sexp) (t1 t2: n_sexp), refltrans R t1 t2 -> refltrans (R !_! R') t1 t2.
Proof.
  intros R R' t1 t2 Hrefl. induction Hrefl.
  - apply refl. assumption.
  - apply rtrans with t2.
    + apply union_left. assumption.
    + assumption.
  - apply rtrans_aeq with t2; assumption.
Qed.

Lemma refltrans_union_equiv: forall (R R1 R2 : Rel n_sexp), (forall (t1 t2 : n_sexp), (R t1 t2 <-> (R1 !_! R2) t1 t2)) -> forall (t1 t2: n_sexp), refltrans (R1 !_! R2) t1 t2 -> refltrans R t1 t2.
Proof.
  intros R R1 R2 H1 t1 t2 H2. induction H2.
  - apply refl. assumption.
  - apply rtrans with t2.
    + apply H1. assumption.
    + assumption.
  - apply rtrans_aeq with t2; assumption.
Qed. 
(* end hide *)
Definition Z_comp_aeq (R :Rel n_sexp) := exists (R1 R2: Rel n_sexp) (f1 f2: n_sexp -> n_sexp), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall t1 t2, R1 t1 t2 -> (f1 t1 =α f1 t2) /\ ((f2 # f1) t1) =α ((f2 # f1) t2)) /\ (forall t1 t2, t1 =α t2 -> ((f2 # f1) t1) =α ((f2 # f1) t2)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).

(** ** Compositional Z property modulo implies Z property modulo *)
Theorem Z_comp_aeq_implies_Z_prop_aeq: forall R, Z_comp_aeq R -> Z_prop_aeq R.
Proof.
  intros R HZ_comp_aeq. unfold Z_comp_aeq, Z_prop_aeq in *. destruct HZ_comp_aeq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 [H4 H5]]]]]]]]]. unfold f_is_weak_Z in H5. exists (f2 # f1). unfold comp in *. split.
  - unfold f_is_Z. intros t1 t2 HR. split.
    + apply Hunion in HR. inversion HR; subst.
      * apply refltrans_composition with (f2 (f1 t2)).
        ** apply refltrans_composition with (f1 t2).
           *** assert (H3' := H3). specialize (H3' t2). pose proof refltrans_union as Hunion'. specialize (Hunion' R1 R2 t2 (f1 t2)). apply Hunion' in H3'. apply refltrans_union_equiv with R1 R2.
               **** apply Hunion.
               **** assumption.
           *** apply H4 with t2. reflexivity.
        ** apply refl. apply aeq_sym. apply H1. assumption.
      * apply H5. assumption.
    + apply Hunion in HR. inversion HR; subst.
      * apply refl. apply H1. assumption.
      * apply H5. assumption.
  - intros t1 t2 Haeq. apply H2. assumption.
Qed.
