(* begin hide *)
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Recdef.

Require Import Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Require Import infra_nom.
(* end hide *)

(** In the $\lambda$-calculus, terms that differ only by the name of bound variables are considered equivalent. This equivalence is called $\alpha$-equivalence, and it is defined by the following inference rules (cf. %\cite{pittsNominalLogicFirst2003}%):

%\begin{mathpar}
\inferrule*[Left={({\rm\it aeq\_var})}]{~}{x =_\alpha x} \and\and \inferrule*[Right={({\rm\it aeq\_abs\_same})}]{t_1 =_\alpha t_2}{\lambda_x.t_1 =_\alpha \lambda_x.t_2} \\
\inferrule*[Right={({\rm\it aeq\_abs\_diff})}]{x \neq y \and x \notin fv(t_2) \and t_1 =_\alpha \swap{y}{x}{t_2}}{\lambda_x.t_1 =_\alpha \lambda_y.t_2} \\
\inferrule*[Right={({\rm\it aeq\_app})}]{t_1 =_\alpha t_1' \and t_2 =_\alpha t_2'}{t_1\ t_2 =_\alpha t_1'\ t_2'}
\end{mathpar}%

We extend this definition to explicit substitutions by adding the following rules:

%\begin{mathpar}
  \inferrule*[Right={({\rm\it aeq\_sub\_same})}]{t_1 =_\alpha t_1' \and t_2 =_\alpha t_2'}{\esub{t_1}{x}{t_2} =_\alpha \esub{t_1'}{x}{t_2'}} \\
\inferrule*[Right={({\rm\it aeq\_sub\_diff})}]{t_2 =_\alpha t_2' \and x \neq y \and x \notin fv(t_1') \and t_1 =_\alpha \swap{y}{x}{t_1'}}{\esub{t_1}{x}{t_2} =_\alpha \esub{t_1'}{y}{t_2'}} 
\end{mathpar}%

In the source code of the formalization, one can find the definition of $\alpha$-equivalence as an inductive relation, together with the proofs of its basic properties, namely reflexivity, symmetry, and transitivity, which together show that $\alpha$-equivalence is indeed an equivalence relation. The formalization also includes lemmas establishing the stability of $\alpha$-equivalence under swapping, as well as its relationship with the set of free variables of a term.
 *)

(* begin hide *)
Reserved Notation "t1 =α t2"
    (at level 60, format "t1  '=α'  t2").

Inductive aeq : Rel n_sexp :=
| aeq_var : forall x, n_var x =α n_var x
| aeq_abs_same : forall x t1 t2, t1 =α t2 ->
                                 n_abs x t1 =α n_abs x t2
| aeq_abs_diff : forall x y t1 t2, x <> y -> x `notin` fv_nom t2 ->
                                   t1 =α (swap y x t2) ->
                                   n_abs x t1 =α n_abs y t2
| aeq_app : forall t1 t2 t1' t2', t1 =α t1' -> t2 =α t2' ->
                                  n_app t1 t2 =α n_app t1' t2'
| aeq_sub_same : forall t1 t2 t1' t2' x, t1 =α t1' -> t2 =α t2' ->  ([x := t2] t1) =α ([x := t2'] t1')
| aeq_sub_diff : forall t1 t2 t1' t2' x y, t2 =α t2' -> x <> y -> x `notin` fv_nom t1' -> t1 =α (swap y x t1') -> ([x := t2] t1) =α ([y := t2'] t1')
where "t =α u" := (aeq t u).

(** The reflexivity of [=α] is straightforward from the definition, and is proved by induction on the structure of [t]:
*)

Lemma aeq_refl : forall t, t =α t.
Proof.
  induction t as [x | x t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 x t2 IHt2 ].
  - apply aeq_var.
  - apply aeq_abs_same; assumption.
  - apply aeq_app; assumption.
  - apply aeq_sub_same; assumption. 
Qed.

(** In addition, this definition is stable under swapping, i.e. [aeq]-equivalent terms remain [aeq]-equivalent after the application of any swap. This property is crucial for proving that [aeq] is an equivalence relation.
The proofs of these lemmas rely on equivariance properties of swapping.
*)

Lemma aeq_stable_swap: forall t1 t2 x y, t1 =α t2 -> (swap x y t1) =α (swap x y t2).
Proof.
  induction 1.
  - apply aeq_var.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply (vswap_neq x y) in H. apply aeq_abs_diff.
    + assumption.
    + apply notin_fv_nom_equivariance. assumption.
    + rewrite <- swap_equivariance. apply IHaeq.
  - simpl. apply aeq_app; assumption.
  - simpl. apply aeq_sub_same; assumption.
  - simpl. apply (vswap_neq x y) in H0. apply aeq_sub_diff.
    + assumption.
    + assumption.
    + apply notin_fv_nom_equivariance. assumption.
    + rewrite <- swap_equivariance. apply IHaeq2. 
Qed.

Lemma aeq_swap_stable: forall t1 t2 x y, (swap x y t1) =α (swap x y t2) -> t1 =α t2.
Proof.
  induction t1 as [z | z t1' | t1' IHt1' t2 IHt2 | t1' IHt1' z t2 IHt2 ].
  - intros t2 x y H. apply (aeq_stable_swap _ _ x y) in H. repeat rewrite swap_involutive in H. assumption.
  - intros t2 x y H. apply (aeq_stable_swap _ _ x y) in H. repeat rewrite swap_involutive in H. assumption.
  - intros t x y H. simpl in *. apply (aeq_stable_swap _ _ x y) in H. simpl in H. repeat rewrite swap_involutive in H. assumption.
  - intros t x y H. apply (aeq_stable_swap _ _ x y) in H. repeat rewrite swap_involutive in H. assumption. 
Qed.

Theorem aeq_swap: forall t1 t2 x y, t1 =α t2 <-> (swap x y t1) =α (swap x y t2).
Proof.
  intros t1 t2 x y. split.
  - apply aeq_stable_swap.
  - apply aeq_swap_stable.
Qed.

Example aeq1 : forall x y, (n_abs x (n_var x)) =α (n_abs y (n_var y)).
Proof.
  intros x y. case (x == y) eqn: Hxy.
  - subst. apply aeq_refl.
  - apply aeq_abs_diff.
    + assumption.
    + simpl. apply notin_singleton. symmetry; assumption.
    + simpl. unfold vswap. rewrite eq_dec_refl. apply aeq_var.
Qed.

Lemma aeq_var_2 : forall x y, (n_var x) =α (n_var y) -> x = y.
Proof.
  intros x y H. inversion H; subst. reflexivity.
Qed.

Lemma aeq_nvar_1: forall t x, t =α (n_var x) -> t = n_var x.
Proof.
  induction t as [z | z t' | t' IHt' t'' IHt'' | t' IHt' z t'' IHt'' ]. 
  - intros x' H. inversion H; subst. reflexivity.
  - intros x' H. inversion H.
  - intros x H. inversion H.
  - intros x' H. inversion H. 
Qed.

Lemma aeq_n_app: forall  t t' t'', n_app t t' =α t'' -> exists u u', t'' = n_app u u'.
Proof.
  intros t t' t'' H. inversion H; subst. exists t1', t2'. reflexivity.
Qed.  

Lemma aeq_n_abs: forall t' t x, n_abs x t =α t' -> exists y t'', t' = n_abs y t''.
Proof.
  induction t' as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros t x Haeq. inversion Haeq.
  - intros t x Haeq. inversion Haeq; subst.
    + exists z, t1. reflexivity.
    + exists z, t1. reflexivity.
  - intros t x Haeq. inversion Haeq.
  - intros t x Haeq. inversion Haeq.
Qed.

Lemma aeq_n_abs2: forall t t' x y, n_abs x t =α n_abs y t' -> t =α (swap x y t').
Proof.
  intros t t' x y H. case (x == y).
  - intro Heq. subst. rewrite swap_id. inversion H; subst.
    + assumption.
    + contradiction.
  - intro Hneq. inversion H; subst.
    + contradiction.
    + rewrite (swap_symmetric _ x y). assumption.
Qed.

Lemma eq_aeq: forall t u, t = u -> t =α u.
Proof.
  intros t u H; rewrite H; apply aeq_refl.
Qed.

Lemma aeq_size: forall t1 t2, t1 =α t2 -> size t1 = size t2.
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq; reflexivity.
  - simpl. rewrite IHaeq. rewrite swap_size_eq. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. rewrite swap_size_eq. reflexivity. 
Qed.

Lemma aeq_fv_nom : forall t1 t2, t1 =α t2 -> fv_nom t1 [=] fv_nom t2.
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. inversion H1; subst; rewrite IHaeq; apply remove_fv_swap; assumption.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. pose proof remove_fv_swap. specialize (H3 x y t1'). apply H3 in H1. inversion H2; subst; rewrite IHaeq1; rewrite IHaeq2; rewrite H1; reflexivity. 
Qed.

Lemma aeq_pure: forall t1 t2, t1 =α t2 -> pure t1 -> pure t2.
Proof.
  intros t1 t2 Haeq Hpure. induction Haeq.
  - assumption.
  - apply pure_abs. apply IHHaeq. inversion Hpure; subst. assumption.
  - apply pure_abs. apply (pure_swap_2 _ y x). apply IHHaeq. inversion Hpure; subst. assumption.
  - inversion Hpure; subst. apply pure_app.
    + apply IHHaeq1; assumption.
    + apply IHHaeq2; assumption.
  - inversion Hpure.
  - inversion Hpure.
Qed.

(** The proof of symmetry of $\alpha$-equivalence uses the stability under swapping and the fact that $\alpha$-equivalent terms have the same set of free variables. *)

Lemma aeq_sym: forall t1 t2, t1 =α t2 -> t2 =α t1.
Proof.
  induction 1.
  - apply aeq_refl.
  - apply aeq_abs_same; assumption.
  - apply aeq_abs_diff.
    + symmetry; assumption.
    + apply notin_fv_nom_swap with x y t2 in H0. apply aeq_fv_nom in H1. rewrite H1; assumption.
    + apply aeq_swap_stable with x y. rewrite swap_involutive. rewrite swap_symmetric. assumption.
  - apply aeq_app; assumption.
  - apply aeq_sub_same; assumption.
  - apply aeq_sub_diff.
    + assumption.
    + symmetry. assumption.
    + apply aeq_fv_nom in H2. rewrite H2. apply notin_fv_nom_swap. assumption.
    + rewrite swap_symmetric. apply aeq_swap_stable with y x. rewrite swap_involutive. assumption. 
Qed.

(** In order to prove the transitivity of $\alpha$-equivalence, we need some auxiliary results. The first one concerns renaming an abstraction with a fresh name. *)

Lemma aeq_abs_swap: forall t x y, y <> x -> y `notin` fv_nom t -> n_abs y (swap x y t) =α n_abs x t.
Proof.
  intros t x y Hneq Hnotin. apply aeq_abs_diff.
  - assumption.
  - assumption.
  - apply aeq_refl.
Qed.

(** If a term [t] does not have free occurrences of neither [x] and [y] then [(swap x y t)] is $\alpha$-equivalent to [t] because, eventually, only bound variables were changed. This is the content of the next lemma, which is proved by induction on the structure of [t]. *)

Lemma aeq_swap_reduction: forall t x y, x `notin` fv_nom t -> y `notin` fv_nom t -> (swap x y t) =α  t.
Proof. 
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y H1 H2. simpl in *. unfold vswap. destruct (z == x). 
    + subst. apply notin_singleton_is_false in H1. contradiction.
    + destruct (z == y). 
      * subst. apply notin_singleton_is_false in H2. contradiction. 
      * apply aeq_refl.
  - intros x y H1 H2. simpl in *. apply notin_remove_1 in H1. apply notin_remove_1 in H2. case (z == x) eqn: Hzx. 
    + subst. destruct H1 as [H1 | H1].
      * unfold vswap. rewrite eq_dec_refl. case (x == y) eqn: Hxy.
        ** subst. destruct H2 as [H2 | H2].
          *** rewrite swap_id. apply aeq_refl.
          *** rewrite swap_id. apply aeq_refl.
        ** destruct H2 as [H2 | H2].
           *** contradiction.
           *** apply aeq_abs_swap.
            **** symmetry. assumption.
            **** assumption.
      * destruct H2 as [H2 | H2]. 
        ** subst. rewrite vswap_id. rewrite swap_id. apply aeq_refl.
        ** unfold vswap. rewrite eq_dec_refl. case (x == y) eqn: Hxy.
           *** subst. rewrite swap_id. apply aeq_refl.
           *** apply aeq_abs_swap.
            **** symmetry. assumption.
            **** assumption.
    + destruct H1 as [H1 | H1].
      * contradiction.
      * destruct H2 as [H2 | H2].
        ** subst. unfold vswap. rewrite Hzx. rewrite eq_dec_refl. rewrite swap_symmetric. apply aeq_abs_swap.
         *** symmetry. assumption.
         *** assumption.
        ** unfold vswap. rewrite Hzx. case (z == y) eqn: Hzy.
           *** subst. rewrite swap_symmetric. apply aeq_abs_swap.
            **** symmetry. assumption.
            **** assumption.
          *** apply aeq_abs_same. apply IHt1; assumption.
  - intros x y H1 H2. simpl in *. assert (H1' := H1). apply notin_union_1 in H1. apply notin_union_2 in H1'. assert (H2' := H2).  apply notin_union_1 in H2. apply notin_union_2 in H2'. apply aeq_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros x y H1 H2. simpl in *. assert (H1' := H1). apply notin_union_1 in H1. apply notin_union_2 in H1'. assert (H2' := H2). apply notin_union_1 in H2. apply notin_union_2 in H2'. apply notin_remove_1 in H1. apply notin_remove_1 in H2. unfold vswap. destruct H1.
    + subst. rewrite eq_dec_refl. destruct H2.
      * subst. repeat rewrite swap_id. apply aeq_refl.
      * case (x == y). 
        ** intro Heq. subst. repeat rewrite swap_id. apply aeq_refl.
        ** intro Hneq. apply aeq_sub_diff.
           *** apply IHt2; assumption.
           *** symmetry; assumption.
           *** assumption.
           *** apply aeq_refl.
    + destruct (z == x).
      * subst. destruct H2.
        ** subst. repeat rewrite swap_id. apply aeq_refl.
        ** case (x == y). 
           *** intro Heq. subst. repeat rewrite swap_id. apply aeq_refl.
           *** intro Hneq. apply aeq_sub_diff.
           **** apply IHt2; assumption.
           **** symmetry; assumption.
           **** assumption.
           **** apply aeq_refl.
      * destruct H2.
        ** subst. rewrite eq_dec_refl. apply aeq_sub_diff.
           *** apply IHt2; assumption.
           *** symmetry; assumption.
           *** assumption.
           *** rewrite swap_symmetric. apply aeq_refl.            
        ** destruct (z == y).
           *** subst. apply aeq_sub_diff.
               **** apply IHt2; assumption.
               **** symmetry; assumption.
               **** assumption.
               **** rewrite swap_symmetric. apply aeq_refl.
           *** apply aeq_sub_same.
               **** apply IHt1; assumption.
               **** apply IHt2; assumption. 
Qed.

Lemma aeq_swap_swap: forall t x y z, z `notin` fv_nom t -> x `notin` fv_nom t -> (swap z x (swap x y t)) =α (swap z y t).
Proof.
  intros t x y z Hfv Hfv'. case (z == y). 
  - intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y x). rewrite swap_involutive. apply aeq_refl. 
  - intro Hneq. case (x == y). 
    + intro Heq. subst. rewrite swap_id. apply aeq_refl. 
    + intro Hneq'. rewrite shuffle_swap. 
      * apply aeq_swap. apply aeq_swap_reduction; assumption.
      * assumption.
      * assumption.
Qed. 

Lemma aeq_trans: forall t1 t2 t3, t1 =α t2 -> t2 =α t3 -> t1 =α t3.
Proof.
  induction t1 as [x | t11 x IH | t11 t12 IH1 IH2 | t11 t12 x IH2 IH1]  using n_sexp_induction.
  - intros t2 t3 H1 H2. inversion H1; subst. assumption.
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_abs_same. replace t11 with (swap x x t11).
        ** apply IH with t0.
           *** reflexivity.
           *** rewrite swap_id; assumption.
           *** assumption.
        ** apply swap_id.
      * apply aeq_abs_diff.
        ** assumption.
        ** assumption.
        ** apply aeq_sym. apply IH with t0.
           *** apply eq_trans with (size t0).
               **** apply aeq_size in H7. rewrite swap_size_eq in H7. symmetry; assumption.
               **** apply aeq_size in H4. symmetry; assumption.
           *** apply aeq_sym; assumption.
           *** apply aeq_sym; assumption.
    + inversion H2; subst.
      * apply aeq_abs_diff.
        ** assumption.
        ** apply aeq_fv_nom in H7. rewrite <- H7; assumption. 
        ** apply aeq_sym. apply IH with (swap y x t0).
           *** apply eq_trans with (size t0).
               **** apply aeq_size in H7. symmetry; assumption.
               **** apply aeq_size in H6. rewrite H6. rewrite swap_size_eq. reflexivity.
           *** apply aeq_sym. apply aeq_stable_swap; assumption.
           *** apply aeq_sym; assumption.
      * case (x == y0).
        ** intro Heq; subst. apply aeq_abs_same. apply (aeq_stable_swap _ _  y0 y) in H9. rewrite swap_involutive in H9. apply aeq_sym. replace t2 with (swap y y t2).
           *** apply IH with (swap y0 y t0).
               **** apply aeq_size in H6. rewrite  H6. apply aeq_size in H9. symmetry. rewrite swap_symmetric. assumption.
               **** apply aeq_sym. rewrite swap_id; assumption.
               **** apply aeq_sym. rewrite swap_symmetric; assumption.
           *** apply swap_id.             
        ** intro Hneq. apply aeq_fv_nom in H9. assert (H4' := H4). rewrite H9 in H4'. apply notin_fv_nom_swap_remove in H4'.           
           *** apply aeq_abs_diff.
               **** assumption.
               **** assumption.
               **** apply aeq_sym. apply IH with (swap y x t0).
                    ***** apply aeq_size in H1. apply aeq_size in H2. simpl in *. inversion H1; subst. inversion H2; subst. symmetry. assumption.
                    ***** inversion H2; subst.
                    ****** apply aeq_swap. apply aeq_sym; assumption.
                    ****** apply (aeq_swap _ _ y x). rewrite swap_involutive. rewrite (swap_symmetric _ y0 x). apply IH with (swap y0 y t2).
                    ******* apply aeq_size in H6. rewrite swap_size_eq in *. rewrite H6. apply aeq_size in H13. rewrite swap_size_eq in *. symmetry; assumption.
                    ******* rewrite (swap_symmetric _  y0 y). apply aeq_swap_swap; assumption.
                    ******* apply aeq_sym. assumption.
                    ***** apply aeq_sym; assumption.
           *** assumption.
           *** assumption.
  - intros t2 t3 H1 H2. inversion H1; subst. inversion H2; subst. apply aeq_app. 
    + apply IH1 with t1'; assumption. 
    + apply IH2 with t2'; assumption. 
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_sub_same.
        ** replace t11 with (swap x x t11).
           *** apply IH1 with t1'.
               **** reflexivity.
               **** rewrite swap_id. assumption.
               **** assumption.
           *** rewrite swap_id. reflexivity.
        ** apply IH2 with t2'; assumption.
      * apply aeq_sub_diff.
        ** apply IH2 with t2'; assumption.
        ** assumption.
        ** assumption.
        ** apply aeq_sym. apply IH1 with t1'.
           *** apply aeq_size in H10. rewrite swap_size_eq in H10. rewrite <- H10. apply aeq_size in H5. symmetry; assumption.
           *** apply aeq_sym; assumption.
           *** apply aeq_sym; assumption.
    + inversion H2; subst.            
      * apply aeq_sub_diff.
        ** apply IH2 with t2'; assumption.
        ** assumption.
        ** apply aeq_fv_nom in H9. rewrite H9 in H7. assumption.
        ** apply (aeq_swap _ _  y x) in H9. apply aeq_sym. apply IH1 with (swap y x t1').
           *** apply aeq_size in H8. rewrite H8. apply aeq_size in H9. rewrite H9. rewrite swap_size_eq. reflexivity.
           *** apply aeq_sym. assumption.
           *** apply aeq_sym. assumption.
      * case (x == y0). 
        ** intro Heq. subst. apply aeq_sub_same.
           *** apply (aeq_swap _ _ y0 y). apply IH1 with t1'.
               **** reflexivity.
               **** apply (aeq_swap _ _ y0 y). rewrite swap_involutive. rewrite (swap_symmetric _ y0 y). assumption.
               **** assumption.
           *** apply IH2 with t2'; assumption.
        ** intro Hneq. apply aeq_sub_diff.
           *** apply IH2 with t2'; assumption.
           *** assumption.
           *** apply aeq_fv_nom in H12. rewrite H12 in H7. apply notin_fv_nom_swap_remove in H7; assumption.
           *** apply (aeq_swap _ _ y x). apply IH1 with t1'.
               **** reflexivity.
               **** apply (aeq_swap _ _ y x). rewrite swap_involutive. assumption.
               **** apply aeq_sym. apply IH1 with (swap y y0 t1'0).
                    ***** apply aeq_size in H8. rewrite swap_size_eq in *. rewrite H8. apply aeq_size in H12. rewrite H12. repeat rewrite swap_size_eq. reflexivity.
                    ***** rewrite (swap_symmetric _ y0 x). apply aeq_swap_swap.
                    ****** assumption.
                    ****** apply aeq_fv_nom in H12. rewrite H12 in H7. apply notin_fv_nom_swap_remove in H7; assumption.
                    ***** apply aeq_sym. rewrite (swap_symmetric _ y y0). assumption. 
Qed.

Instance Equivalence_aeq: Equivalence aeq.
Proof.
  split.
  - unfold Reflexive. apply aeq_refl.
  - unfold Symmetric. apply aeq_sym.
  - unfold Transitive. apply aeq_trans.
Qed.
(* end hide *)
