(* Infrastructure *)
(* begin hide *)
Require Export Arith Lia.  
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Require Import Recdef.

Require Import infra_nom.
Require Import aeq_equiv_es.

Function subst_rec_fun (t:n_sexp) (u :n_sexp) (x:atom) {measure size t} : n_sexp :=
  match t with
  | n_var y => if (x == y) then u else t
  | n_abs y t1 => if (x == y) then t else let (z,_) :=
    atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in n_abs z (subst_rec_fun (swap y z t1) u x)
  | n_app t1 t2 => n_app (subst_rec_fun t1 u x) (subst_rec_fun t2 u x)
  | n_sub t1 y t2 => if (x == y) then n_sub t1 y (subst_rec_fun t2 u x) else let (z,_) :=
    atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
    n_sub (subst_rec_fun (swap y z t1) u x) z (subst_rec_fun t2 u x) end.
Proof.
 - intros. simpl. rewrite swap_size_eq. auto.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. rewrite swap_size_eq. lia.
Defined.

Definition m_subst (u : n_sexp) (x:atom) (t:n_sexp) :=
  subst_rec_fun t u x.
Notation "{ x := u } t" := (m_subst u x t) (at level 60).

Lemma m_subst_var_eq: forall u x, {x := u}(n_var x) = u.
Proof.
  intros u x. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_var_neq: forall u x y, x <> y -> {y := u}(n_var x) = n_var x.
Proof.
  intros u x y H. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y == x) eqn:Hxy.
  - subst. contradiction.
  - reflexivity.
Qed.

Lemma m_subst_app: forall t1 t2 u x, {x := u}(n_app t1 t2) = n_app ({x := u}t1) ({x := u}t2).
Proof.
  intros t1 t2 u x. unfold m_subst. rewrite subst_rec_fun_equation. reflexivity.
Qed.

Lemma aeq_m_subst_notin: forall t u x, x `notin` fv_nom t -> {x := u}t =α t.
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y ] using n_sexp_induction. 
  - intros u x Hfv. simpl in *. apply notin_singleton_1 in Hfv. rewrite m_subst_var_neq.
    + apply aeq_refl.
    + assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y). 
    + subst. apply aeq_refl. 
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))) as [z]. case (z == y). 
      * intro Heq. subst. apply aeq_abs_same. apply aeq_trans with (swap y y t1).
        ** apply H. 
           *** reflexivity.
           *** rewrite swap_id. apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** assumption.
        ** rewrite swap_id. apply aeq_refl. 
      * intro Hneq. apply aeq_abs_diff. 
        ** assumption.
        ** apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
           *** subst. contradiction.
           *** assumption.
        ** apply H.
           *** reflexivity.
           *** apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply notin_fv_nom_swap_neq; assumption.
  - intros u x Hfv. unfold m_subst in *. simpl in *. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt2. apply notin_union_1 in Hfv. assumption.
    + apply IHt1. apply notin_union_2 in Hfv. assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))). destruct (x == y). 
    + subst. apply aeq_sub_same.
      * apply aeq_refl.
      * apply notin_union_2 in Hfv. apply IHt1. assumption.
    + case (x0 == y).
      * intro Heq. subst. apply aeq_sub_same.
        ** apply aeq_trans with (swap y y t1). apply H.
           *** reflexivity.
           *** rewrite swap_id. apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** assumption.
           *** rewrite swap_id. apply aeq_refl.
        ** apply IHt1. apply notin_union_2 in Hfv. assumption.
      * intro Hneq. apply aeq_sub_diff.
        ** apply IHt1. apply notin_union_2 in Hfv. assumption.
        ** assumption.
        ** apply notin_union_2 in n. apply notin_union_1 in n. simpl in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
           *** symmetry in H0. contradiction.
           *** assumption.
        ** apply H.
           *** reflexivity.
           *** apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv. 
               **** symmetry in H0. contradiction. 
               **** repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply notin_fv_nom_swap_neq; assumption.
Qed.

Lemma aeq_m_subst_abs: forall t u x y, {x := u}(n_abs y t) =α if (x == y) then (n_abs y t) else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t) `union` {{x}}) in n_abs z (subst_rec_fun (swap y z t) u x).
Proof.
  intros t u x y. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + simpl. contradiction.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). apply aeq_refl.
Qed.

Lemma aeq_m_subst_sub: forall t1 t2 u x y, {x := u}(n_sub t1 y t2) =α if (x == y) then (n_sub t1 y ({x := u}t2)) else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_sub t1 y t2) `union` {{x}}) in n_sub ({x := u}(swap y z t1)) z ({x := u}t2).
Proof.
  intros. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + simpl. contradiction.
    + simpl. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))). apply aeq_refl.
Qed.

Lemma m_subst_abs_eq: forall u x t, {x := u}(n_abs x t) = n_abs x t.
Proof.
  intros u x t. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_sub_eq: forall u x t1 t2, {x := u}(n_sub t1 x t2) = n_sub t1 x ({x := u}t2).
Proof.
  intros u x t1 t2. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma fv_nom_remove: forall t u x y, y `notin` fv_nom u -> y `notin` remove x (fv_nom t) -> y `notin` fv_nom ({x := u}t).
Proof.
    intros t u x y H0 H1. unfold m_subst. functional induction (subst_rec_fun t u x).
  - assumption.
  - apply notin_remove_1 in H1. destruct H1.
    + subst. simpl. apply notin_singleton. symmetry; assumption.
    + assumption.
  - simpl in *. rewrite double_remove in H1. assumption.
  - simpl in *. case (y == z).
    + intro Heq. subst. apply notin_remove_3; reflexivity.
    + intro Hneq. apply notin_remove_2. apply IHn.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1.
        ** subst. apply notin_remove_3; reflexivity.
        ** clear IHn e1 e0. case (y == x).
           *** intro Heq. subst. apply notin_remove_3; reflexivity.
           *** intro Hneq'. apply notin_remove_2. apply notin_remove_1 in H. destruct H.
               **** subst. apply notin_fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                    ***** contradiction.
                    ***** assumption.
               **** case (y == y0).
                    ***** intro Heq. subst. apply notin_fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                    ****** contradiction.
                    ****** assumption.
                    ***** intro Hneq''. apply notin_fv_nom_swap_neq; assumption.
  - simpl in *. apply notin_union_3. 
    + apply IHn.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1. 
        ** subst. apply notin_remove_3'; reflexivity.
        ** apply notin_union_1 in H. apply notin_remove_2. assumption.
    + apply IHn0.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1. 
        ** subst. apply notin_remove_3'. reflexivity.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_union_3. 
    + apply notin_remove_1 in H1. destruct H1.
      * subst. apply notin_remove_3'. reflexivity.
      * simpl. apply notin_union_1 in H. assumption.
    + apply IHn. 
      * assumption. 
      * apply notin_remove_1 in H1. destruct H1.
        ** subst. apply notin_remove_3'. reflexivity.
        ** simpl. apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_remove_1 in H1. destruct H1.
    + subst. apply notin_union_3.
      * case (y == z).
        ** intros Heq. subst. apply notin_remove_3'; reflexivity.
        ** intros Hneq. apply notin_remove_2. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. 
           apply IHn.
          *** assumption.
          *** apply notin_remove_3; reflexivity.
      * simpl. apply IHn0. 
        ** assumption.
        ** apply notin_remove_3; reflexivity.
    + simpl. apply notin_union_3.
      * case (y == z). 
        ** intro Heq. subst. apply notin_remove_3; reflexivity.
        ** intro Hneq. apply notin_remove_2. apply notin_union_1 in H. apply IHn.
            *** assumption.
            *** apply notin_remove_1 in H. destruct H.
                **** simpl. subst. apply notin_remove_2. apply notin_fv_nom_swap. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                     ***** contradiction.
                     ***** assumption.
                **** apply notin_remove_2. case (y == y0). 
                     ***** intro Heq. subst. apply notin_fv_nom_swap. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                     ****** contradiction.
                     ****** assumption.
                     ***** intro Hneq'. apply notin_fv_nom_swap_neq.
                     ****** assumption.
                     ****** assumption.
                     ****** assumption.
      * apply IHn0.
        ** assumption.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
Qed.

Corollary fv_nom_remove_eq: forall t1 t2 x, x `notin` fv_nom t2 -> x `notin` fv_nom ({x := t2} t1).
Proof.
  intros t1 t2 x Hnotin. apply fv_nom_remove.
  - assumption.
  - apply notin_remove_3. reflexivity.
Qed.

Lemma pure_m_subst : forall t u x, pure t -> pure u -> pure ({x := u}t).
Proof.
  induction t as [y | t1 y IHt1 | t1 t2 IHt1 IHt2 | t1 t2 y IHt1 IHt2] using n_sexp_induction.
  - intros u x H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + assumption.
  - intros u x H1 H2. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))) as [z Hnotin]. apply pure_abs. inversion H1; subst. pose proof pure_swap as H'. specialize (H' y z t1). pose proof H0 as H''. apply H' in H''. clear H'. apply IHt1.
      * reflexivity.
      * assumption.
      * assumption.
  - intros u x Happ Hpure. inversion Happ; subst. unfold m_subst in *. rewrite subst_rec_fun_equation. apply pure_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros u x Hsubst Hpure. inversion Hsubst. 
Qed. 

Axiom Eq_implies_equality: forall t1 t2, t1 =α t2 -> fv_nom t1 = fv_nom t2.

Lemma aeq_m_subst_in: forall t u u' x, u =α u' -> ({x := u}t) =α ({x := u'}t).
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y ] using n_sexp_induction. 
  - intros u u' x Haeq. unfold m_subst. repeat rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + apply aeq_refl.
  - intros u u' x Haeq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y). 
    + apply aeq_refl. 
    + pose proof Haeq as Hfv. apply Eq_implies_equality in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs y t1)) (singleton x)))). apply aeq_abs_same. apply H. 
      * reflexivity.
      * assumption.
  - intros u u' x Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt2. apply aeq_sym. assumption.
    + apply IHt1. apply aeq_sym. assumption.
  - intros u u' x Haeq. case (x == y).
    + intro Heq. subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_same.
      * apply aeq_refl.
      * apply IHt1. assumption.
    + intro Hneq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y).
      * contradiction.
      * pose proof Haeq as Hfv. apply Eq_implies_equality in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom ([y := t2]t1)) (singleton x)))). apply aeq_sub_same.     
        ** apply H.
           *** reflexivity.
           *** apply aeq_sym. assumption.
        ** apply IHt1. apply aeq_sym. assumption.
Qed. 
       
Lemma aeq_sub_notin: forall t1 t1' t2 t2' x y, x <> y ->  n_sub t1 x t2 =α n_sub t1' y t2' -> x `notin` fv_nom t1'.
Proof.
  intros t1 t1' t2 t2' x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.

Lemma aeq_m_subst_out: forall t t' u x, t =α t' -> ({x := u}t) =α ({x := u}t').
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y] using n_sexp_induction. 
  - intros t' u x Haeq. inversion Haeq; subst. apply aeq_refl.
  - intros t' u x Haeq. inversion Haeq; subst. 
    + case (x == y).  
      * intro Heq. subst. repeat rewrite m_subst_abs_eq. assumption. 
      * intro Hneq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y).
        ** contradiction.
        ** simpl. pose proof H3 as Haeq'. apply Eq_implies_equality in H3. rewrite H3. destruct (atom_fresh (union (fv_nom u) (union (remove y (fv_nom t2)) (singleton x)))) as [z]. apply aeq_abs_same. apply H.
           *** reflexivity. 
           *** apply aeq_swap. assumption. 
    + case (x == y). 
      * intro Heq. subst. rewrite m_subst_abs_eq. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (y == y0).
        ** contradiction.
        ** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y0 t2)) (singleton y)))) as [x]. apply aeq_trans with (n_abs x (swap y0 x t2)).
           *** apply aeq_trans with (n_abs y0 t2). 
               **** assumption.
               **** case (x == y0).
                    ***** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq. apply aeq_abs_diff.
                    ****** symmetry. assumption.
                    ****** apply notin_fv_nom_swap. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* assumption.
                    ****** rewrite (swap_symmetric _ y0 x). rewrite swap_involutive. apply aeq_refl.
           *** apply aeq_abs_same. apply aeq_sym. apply aeq_m_subst_notin. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply notin_fv_nom_swap_neq; assumption. 
      * intro Hneq. case (x == y0).
        ** intro Heq. subst. rewrite m_subst_abs_eq. apply aeq_trans with (n_abs y t1).
           *** apply aeq_m_subst_notin. apply aeq_fv_nom in Haeq. rewrite Haeq. simpl. apply notin_remove_3. reflexivity.
           *** assumption.
        ** intro Hneq'. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y).
           *** contradiction.
           *** destruct (x == y0).
               **** contradiction.
               **** pose proof Haeq as Hfv. apply Eq_implies_equality in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y0 t2)) (singleton x)))) as [x0]. apply  aeq_abs_same. apply H. 
                    ***** reflexivity.
                    ***** apply (aeq_swap _ _ y x0) in H5. rewrite H5. case (x0 == y0).
                    ****** intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y y0). rewrite swap_involutive. apply aeq_refl.
                    ****** intro Hneq''. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). apply aeq_swap_swap.
                    ******* apply notin_union_2 in n1. apply notin_union_1 in n1. simpl in n1. apply notin_remove_1 in n1. destruct n1.
                    ******** symmetry  in H0. contradiction.
                    ******** assumption.
                    ******* assumption. 
  - intros t u x Haeq. inversion Haeq; subst. clear Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply aeq_sym. apply IHt2. assumption.
    + apply aeq_sym. apply IHt1. assumption.
  - intros t u x Haeq. inversion Haeq; subst. 
    + case (x == y). 
      * intro Heq. subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_same. 
        ** assumption.
        ** apply IHt1. assumption. 
      * intro Hneq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y).
        ** contradiction.
        ** pose proof H4 as Hfvt1. apply Eq_implies_equality in Hfvt1. pose proof H5 as Hfvt2. apply Eq_implies_equality in Hfvt2. simpl. rewrite Hfvt1. rewrite Hfvt2. destruct (atom_fresh (union (fv_nom u) (union (union (remove y (fv_nom t1')) (fv_nom t2')) (singleton x)))). apply aeq_sub_same.
           *** apply H. 
               **** apply aeq_size in H4. symmetry. assumption.
               **** apply aeq_swap. apply aeq_sym. assumption.
           *** apply aeq_sym. apply IHt1. assumption.
    + case (x == y). 
      * intro Heq. subst. rewrite m_subst_sub_eq. case (y == y0). 
        ** intro Heq. subst. contradiction. 
        ** intro Hneq. unfold m_subst in *. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (y == y0).
           *** contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y0 := t2'] t1')) (singleton y)))). apply aeq_sub_diff.
               **** apply aeq_sym. apply IHt1. assumption. 
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. symmetry. assumption.
               **** pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply (aeq_swap _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite <- H7 in n0. rewrite <- H7 in H6. case (x == y0).
                    ***** intro Heq. subst. apply notin_fv_nom_swap_2 in H6. assumption.
                    ***** intro Hneq'. apply notin_remove_1 in n0.
                    ****** destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* apply notin_fv_nom_swap_remove in H0.
                    ******** assumption.
                    ******** repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. symmetry. assumption.
                    ******** assumption.
               **** apply aeq_trans with (swap y0 x t1'). 
                    ***** apply aeq_m_subst_notin. apply notin_fv_nom_swap_neq.
                    ****** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                    ****** assumption.
                    ****** assumption.
                    ***** apply (aeq_swap _ _ y x) in H7. rewrite H7.  apply aeq_sym. rewrite (swap_symmetric _ y x). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x). case (x == y0).
                    ****** intro Heq. subst. rewrite (swap_symmetric _ y0 y). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* assumption.  
      * intro Hneq. case (x == y0).
        ** intro Heq. subst. rewrite m_subst_sub_eq. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y0 == y).
           *** contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y := t2] t1)) (singleton y0)))). apply aeq_sub_diff.
               **** apply IHt1. assumption. 
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. symmetry. assumption.
               **** pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply (aeq_swap _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite <- H7. case (x == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y0 y). apply notin_fv_nom_swap. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq.
                    ****** assumption.
                    ****** assumption.
                    ***** intro Hneq'. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* apply notin_fv_nom_swap_neq.
                    ******** assumption.
                    ******** repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. symmetry. assumption.
                    ******** assumption.
               **** apply aeq_trans with (swap y x t1). 
                    ***** apply aeq_m_subst_notin. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq. 
                    ****** apply notin_fv_nom_swap_neq.
                    ******* repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                    ******* assumption.
                    ******* assumption.
                    ****** assumption.
                    ***** apply (aeq_swap _ _ y x) in H7. rewrite H7. rewrite (swap_symmetric _ y x). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x). case (x == y).
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    *******  pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H0. contradiction.
                    ******** apply aeq_swap in H7. apply aeq_sym in H7. apply (aeq_swap _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite H7. apply notin_fv_nom_swap_neq.
                    ********* assumption.  
                    ********* repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. symmetry. assumption.
                    ********* assumption.
                    ******* assumption.
        ** intro Hneq'. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y).
           *** contradiction.
           *** apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y0).
               **** contradiction.
               ****  apply Eq_implies_equality in Haeq. simpl in *. rewrite Haeq. destruct (atom_fresh (union (fv_nom u) (union (union (remove y0 (fv_nom t1')) (fv_nom t2')) (singleton x)))). apply aeq_sub_same.
                    ***** apply H.
                    ****** apply aeq_size in H7. rewrite swap_size_eq in H7. symmetry. assumption.
                    ****** apply (aeq_swap _ _ y x0) in H7. rewrite H7. apply aeq_sym. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). case (x0 == y0).
                    ******* intro Heq. subst. rewrite (swap_symmetric _ y0 y). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ******* intro Hneq''. apply aeq_swap_swap.
                    ******** apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1. subst. contradiction.
                    ********* assumption.
                    ******** assumption.
                    ***** apply aeq_sym. apply IHt1. assumption.
Qed.

Corollary aeq_m_subst_eq: forall t t' u u' x, t =α t' -> u =α u' -> ({x := u}t) =α ({x := u'}t').
Proof.
  intros t t' u u' x H1 H2. apply aeq_trans with ({x:=u}t').
  - apply aeq_m_subst_out. assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

Lemma aeq_swap_m_subst: forall x y z t u, swap x y ({z := u}t) =α ({(vswap x y z) := (swap x y u)}(swap x y t)).
Proof.
  intros x y z t u. destruct (x == y). 
  - subst. repeat rewrite swap_id. rewrite vswap_id. apply aeq_refl.
  - generalize dependent u. generalize dependent z. generalize dependent y. generalize dependent x. induction t as  [y' | t1 y' | t1 t2 | t1 t2 y'] using n_sexp_induction.    
    + intros x y Hneq z u. unfold m_subst. rewrite subst_rec_fun_equation. destruct (z == y').
      * subst. simpl swap at 2. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
      * pose proof n as Hswap. apply (vswap_neq x y) in n. simpl swap at 2. rewrite subst_rec_fun_equation. destruct (vswap x y z == vswap x y y').
        ** contradiction.
        ** simpl swap. apply aeq_refl.
    + intros x y Hneq z u. simpl. case (y' == z). 
      * intro Heq. subst. repeat rewrite m_subst_abs_eq. simpl. apply aeq_refl. 
      * intro Hneq'. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (vswap_neq x y) in n. contradiction.
           *** simpl. destruct (atom_fresh (union (fv_nom u) (union (remove y' (fv_nom t1)) (singleton z)))) as [x0]. destruct (atom_fresh (union (fv_nom (swap x y u)) (union (remove (vswap x y y') (fv_nom (swap x y t1))) (singleton (vswap x y z))))) as [x1]. simpl. case (x1 == vswap x y x0).
               **** intro Heq. subst. apply aeq_abs_same. rewrite H. 
                    ***** rewrite <- swap_equivariance. apply aeq_refl.
                    ***** reflexivity.
                    ***** assumption.
               **** intro Heq''. apply aeq_abs_diff.  
                    ***** symmetry; assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. pose proof n1 as Hx0. case (y' == x0).
                    ******** intro Heq. subst. apply notin_fv_nom_remove_swap_inc. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ********* symmetry in H0. contradiction.
                    ********* assumption.
                    ******** intros Hneq'''. apply notin_fv_nom_swap_neq.
                    ********* symmetry; assumption.
                    ********* symmetry. apply vswap_neq. assumption.
                    ********* apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********** contradiction.
                    ********** apply notin_fv_nom_equivariance. assumption. 
                    ***** rewrite H. 
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq'''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply aeq_swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (vswap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* repeat rewrite swap_size_eq. reflexivity.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
    + intros x y H z u. unfold m_subst in *. rewrite subst_rec_fun_equation. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_sym. apply aeq_app.
      * apply IHt2. assumption.
      * apply IHt1. assumption.
    + intros x y Hneq z u. simpl. case (y' == z). 
      * intro Heq. subst. repeat rewrite m_subst_sub_eq. simpl. apply aeq_sub_same. 
        ** apply aeq_refl.
        ** apply IHt1. assumption.
      * intro Hneq'. unfold m_subst. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (vswap_neq x y) in n. contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y' t2)) (singleton z)))). destruct (atom_fresh (union (fv_nom (swap x y u)) (union (fv_nom (n_sub (swap x y t1) (vswap x y y') (swap x y t2))) (singleton (vswap x y z))))). simpl in *. apply aeq_sym. case (x1 == vswap x y x0). 
               **** intro Heq. subst. apply aeq_sub_same. 
                    ***** rewrite <- swap_equivariance. apply H.
                    ****** reflexivity.
                    ****** assumption.
                    ***** apply IHt1. assumption.
               **** intro Hneq''. apply aeq_sub_diff.
                    ***** apply IHt1. assumption. 
                    ***** symmetry; assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. case (y' == x0).
                    ******* intro Heq. subst. apply notin_fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* intro Hneq'''. apply notin_fv_nom_swap_neq.
                    ******** symmetry; assumption.
                    ******** apply (vswap_neq x y) in Hneq'''. symmetry; assumption.
                    ******** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********* contradiction.
                    ********* assumption.
                    ***** unfold m_subst in *. rewrite H. 
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq'''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq''''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply aeq_swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (vswap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* repeat rewrite swap_size_eq. reflexivity.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
Qed.

Lemma aeq_swap_subst_rec_fun: forall x y z t u, swap x y ({z := u}t) =α ({(vswap x y z) := (swap x y u)}(swap x y t)).
Proof.
  intros x y z t u. destruct (x == y). 
  - subst. repeat rewrite swap_id. rewrite vswap_id. apply aeq_refl.
  - generalize dependent u. generalize dependent z. generalize dependent y. generalize dependent x. induction t as  [y' | t1 y' | t1 t2 | t1 t2 y'] using n_sexp_induction.    
    + intros x y Hneq z u. unfold m_subst. rewrite subst_rec_fun_equation. destruct (z == y').
      * subst. simpl swap at 2. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
      * pose proof n as Hswap. apply (vswap_neq x y) in n. simpl swap at 2. rewrite subst_rec_fun_equation. destruct (vswap x y z == vswap x y y').
        ** contradiction.
        ** simpl swap. apply aeq_refl.
    + intros x y Hneq z u. simpl. case (y' == z). 
      * intro Heq. subst. repeat rewrite m_subst_abs_eq. simpl. apply aeq_refl. 
      * intro Hneq'. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (vswap_neq x y) in n. contradiction.
           *** simpl. destruct (atom_fresh (union (fv_nom u) (union (remove y' (fv_nom t1)) (singleton z)))) as[x0]. destruct (atom_fresh (union (fv_nom (swap x y u)) (union (remove (vswap x y y') (fv_nom (swap x y t1))) (singleton (vswap x y z))))) as [x1]. simpl. case (x1 == vswap x y x0).
               **** intro Heq. subst. apply aeq_abs_same. rewrite H. 
                    ***** rewrite <- swap_equivariance. apply aeq_refl.
                    ***** reflexivity.
                    ***** assumption.
               **** intro Heq''. apply aeq_abs_diff.  
                    ***** symmetry. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. pose proof n1 as Hx0. case (y' == x0).
                    ******** intro Heq. subst. apply notin_fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ********* symmetry in H0. contradiction.
                    ********* assumption.
                    ******** intros Hneq'''. apply notin_fv_nom_swap_neq.
                    ********* symmetry. assumption.
                    ********* symmetry. apply vswap_neq. assumption.
                    ********* apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********** contradiction.
                    ********** apply notin_fv_nom_equivariance. assumption. 
                    ***** rewrite H. 
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq'''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply aeq_swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (vswap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* rewrite swap_size_eq. reflexivity.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
    + intros x y H z u. unfold m_subst in *. rewrite subst_rec_fun_equation. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_sym. apply aeq_app.
      * apply IHt2. assumption.
      * apply IHt1. assumption.
    + intros x y Hneq z u. simpl. case (y' == z). 
      * intro Heq. subst. repeat rewrite m_subst_sub_eq. simpl. apply aeq_sub_same. 
        ** apply aeq_refl.
        ** apply IHt1. assumption.
      * intro Hneq'. unfold m_subst. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (vswap_neq x y) in n. contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y' t2)) (singleton z)))). destruct (atom_fresh (union (fv_nom (swap x y u)) (union (fv_nom (n_sub (swap x y t1) (vswap x y y') (swap x y t2))) (singleton (vswap x y z))))). simpl in *. apply aeq_sym. case (x1 == vswap x y x0). 
               **** intro Heq. subst. apply aeq_sub_same. 
                    ***** rewrite <- swap_equivariance. apply H.
                    ****** reflexivity.
                    ****** assumption.
                    ***** apply IHt1. assumption.
               **** intro Hneq''. apply aeq_sub_diff.
                    ***** apply IHt1. assumption. 
                    ***** symmetry. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. case (y' == x0).
                    ******* intro Heq. subst. apply notin_fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* intro Hneq'''. apply notin_fv_nom_swap_neq.
                    ******** symmetry. assumption.
                    ******** apply (vswap_neq x y) in Hneq'''. symmetry. assumption.
                    ******** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********* contradiction.
                    ********* assumption.
                    ***** unfold m_subst in *. rewrite H. 
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq'''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq''''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply aeq_swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (vswap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* rewrite swap_size_eq. reflexivity.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
Qed.
(* end hide *)

Lemma aeq_m_subst_abs_neq: forall t u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom (n_abs y t) `union` {{x}} -> {x := u}(n_abs y t) =α n_abs z ({x := u}(swap y z t)).
Proof.
  intros t u x y z H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
  - subst. contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). case (x0 == z).
    + intro Heq. subst. apply aeq_refl.
    + intro Hneq. apply aeq_abs_diff.
      * assumption.
      * apply fv_nom_remove.
        ** apply notin_union_1 in n0. assumption.
        ** simpl in *. case (x0 == y).
           *** intro Heq. subst. apply notin_remove_2. apply notin_fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_remove_1 in H2. destruct H2.
               **** contradiction.
               **** assumption.
           *** intro Hneq'. apply notin_remove_2. apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
               **** symmetry in H. contradiction.
               **** apply notin_fv_nom_swap_neq; assumption.
      * apply aeq_sym. apply aeq_trans with (subst_rec_fun (swap z x0 (swap y z t)) (swap z x0 u) (vswap z x0 x)).
        ** apply aeq_swap_subst_rec_fun.
        ** replace (vswap z x0 x) with x.
           *** apply aeq_m_subst_eq.
               **** rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). case (x0 == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y z). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq'. case (z == y).
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq''. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
                    ******* apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_remove_1 in H2. destruct H2.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
               **** apply aeq_swap_reduction.
                    ***** apply notin_union_1 in H2. assumption.
                    ***** apply notin_union_1 in n0. assumption.
           *** unfold vswap. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. default_simp.
Qed.               

(* begin hide *)
Corollary aeq_m_subst_n_abs_neq_notin: forall t1 t2 x y, x <> y -> x `notin` fv_nom t2 -> {y := t2} (n_abs x t1) =α n_abs x ({y := t2} t1).
Proof.
  intros t1 t2 x y Hneq Hnotin. apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1) (Metatheory.union (singleton y) (singleton x))))) in n_abs z ({y := t2} (swap z x t1))).
  - default_simp. rewrite (swap_symmetric _ x0 x). apply aeq_m_subst_abs_neq.
    + symmetry; assumption.
    + apply notin_union.
      * apply notin_union_1 in n. assumption.
      * apply notin_union.
        ** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
        ** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
  - default_simp. apply aeq_abs_diff.
    + repeat apply notin_union_2 in n. apply notin_singleton_1 in n. symmetry; assumption.
    + apply fv_nom_remove.
      * apply notin_union_1 in n. assumption.
      * apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
    + apply aeq_trans with ({(vswap x0 x y) := swap x0 x t2} (swap x0 x t1)).
      * unfold vswap. destruct (y == x0).
        ** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. contradiction.
        ** destruct (y == x).
           *** symmetry in e. contradiction.
           *** apply aeq_m_subst_in. apply aeq_sym. apply aeq_swap_reduction.
               **** apply notin_union_1 in n. assumption.
               **** assumption.
      * apply aeq_sym. rewrite (swap_symmetric _ x x0). apply aeq_swap_m_subst.
Qed. 

Lemma aeq_m_subst_sub_neq : forall t1 t2 u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom ([y := t2]t1) `union` {{x}} -> {x := u}([y := t2]t1) =α ([z := ({x := u}t2)]({x := u}(swap y z t1))).
Proof.
  intros t1 t2 u x y z H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y). 
  - contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y := t2]t1)) (singleton x)))). destruct (x0 == z).
    + subst. apply aeq_refl.
    + apply aeq_sub_diff.
      * apply aeq_refl.
      * assumption.
      * apply fv_nom_remove. 
        ** apply notin_union_1 in n0. assumption.
        ** simpl in *. case (x0 == y). 
           *** intro Heq. subst. apply notin_remove_2. apply notin_fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. apply notin_union_1 in H2. apply notin_remove_1 in H2. destruct H2.
               **** contradiction.
               **** assumption.
           *** intro Hneq. apply notin_remove_2. apply notin_fv_nom_swap_neq. 
               **** assumption.
               **** assumption.
               **** apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply diff_remove_2 in n0; assumption.
      * apply aeq_sym. apply aeq_trans with (subst_rec_fun (swap z x0 (swap y z t1)) (swap z x0 u) (vswap z x0 x)). 
        ** apply aeq_swap_subst_rec_fun.
        ** replace (vswap z x0 x) with x. 
           *** apply aeq_m_subst_eq. 
               **** rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). simpl in *. case (x0 == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y z). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq. case (z == y). 
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
                    ******* apply notin_union_2 in H2. apply notin_union_1 in H2. apply notin_union_1 in H2. apply notin_remove_1 in H2. destruct H2.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
               **** apply aeq_swap_reduction.
                    ***** apply notin_union_1 in H2. assumption.
                    ***** apply notin_union_1 in n0. assumption.
           *** unfold vswap. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. default_simp.
Qed.

Lemma aeq_double_m_subst: forall t t1 t2 x, {x := t1}({x := t2}t) =α ({x := ({x := t1}t2)}t).
Proof.
 intros. induction t using n_sexp_size_induction.
    - destruct (x0 == x).
      + subst. repeat rewrite m_subst_var_eq. apply aeq_refl.
      + repeat rewrite m_subst_var_neq; try assumption. apply aeq_refl.
    - destruct (x == z).
      + subst. repeat rewrite m_subst_abs_eq. apply aeq_refl.
      + apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2)
               (Metatheory.union (fv_nom (n_abs z t)) (singleton x))))) in ({x := t1}(n_abs z0 ({x := t2} swap z z0 t)))).
        * default_simp. apply aeq_m_subst_out. apply aeq_m_subst_abs_neq.
          ** assumption.
          ** apply notin_union_3; auto.
        * default_simp. pose proof aeq_m_subst_abs_neq.  apply aeq_trans with (n_abs x0 ({x := {x := t1} t2} (swap z x0 t))).
          ** apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2)
               (Metatheory.union (fv_nom (n_abs z t)) (Metatheory.union (singleton x0) (Metatheory.union (singleton x) (singleton z))))))) in (n_abs z0 ({x := t1} (swap x0 z0 ({x := t2} swap z x0 t))))).
            *** default_simp. apply aeq_m_subst_abs_neq; auto. apply notin_union_3.
              **** auto.
              **** apply notin_union_3; try auto. simpl. apply notin_remove_2. apply fv_nom_remove.
                ***** auto.
                ***** apply notin_remove_2. apply notin_fv_nom_swap_neq; auto.
            *** default_simp. apply aeq_abs_diff.
              **** auto.
              **** apply fv_nom_remove.
                ***** apply fv_nom_remove; auto.
                ***** apply notin_remove_2. apply notin_fv_nom_swap_neq; auto.
              **** apply aeq_trans with ({x := t1} ({vswap x0 x1 x := swap x0 x1 t2} swap x0 x1 (swap z x0 t))).
                ***** apply aeq_m_subst_out. apply aeq_swap_m_subst.
                ***** assert (Hneq: x <> x0). auto. assert (Hneq2: x <> x1). auto. 
                      unfold vswap. destruct (x == x0); try contradiction. destruct (x == x1); try contradiction. apply aeq_trans with ({x := t1} ({x := t2} swap x0 x1 (swap z x0 t))).
                  ****** apply aeq_m_subst_out. apply aeq_m_subst_in. apply aeq_swap_reduction; try auto.
                  ****** apply aeq_trans with ({vswap x0 x1 x := swap x0 x1 ({x := t1} t2)} swap x0 x1 (swap z x0 t)).
                    ******* unfold vswap. destruct (x == x0); try contradiction. destruct (x == x1); try contradiction. apply aeq_trans with ({x := ({x := t1} t2)} swap x0 x1 (swap z x0 t)).
                      ******** apply H. repeat rewrite swap_size_eq. lia.
                      ******** apply aeq_m_subst_in. pose proof aeq_swap_m_subst. specialize (H1 x0 x1 x t2 t1). apply aeq_trans with ({vswap x0 x1 x := swap x0 x1 t1} swap x0 x1 t2).
                        *********  unfold vswap. destruct (x == x0); try contradiction. destruct (x == x1); try contradiction. apply aeq_m_subst_eq.
                          ********** apply aeq_sym. apply aeq_swap_reduction; auto.
                          ********** apply aeq_sym. apply aeq_swap_reduction; auto.
                        ********* apply aeq_sym. apply aeq_swap_m_subst.
                    ******* apply aeq_sym. apply aeq_swap_m_subst.
          ** apply aeq_sym. apply aeq_m_subst_abs_neq; try assumption. apply notin_union_3.
            *** apply fv_nom_remove; auto.
            *** auto.
    - repeat rewrite m_subst_app. apply aeq_app.
      + apply H. simpl. lia.
      + apply H. simpl. lia.
    - destruct (x == z).
      + subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_same.
        * reflexivity.
        * apply H. simpl. lia.
      + apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t4)
               (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2) (Metatheory.union (singleton z) 
              (singleton x))))))) in (({x := t1} ([z0 := {x := t2} t4] ({x := t2} swap z z0 t3))))).
        * default_simp. apply aeq_m_subst_out. apply aeq_m_subst_sub_neq; default_simp.
        * default_simp. apply aeq_trans with ([x0 := {x := {x := t1} t2} t4] ({x := {x := t1} t2} swap z x0 t3)).
          ** apply aeq_trans with ([x0 := {x := t1} ({x := t2} t4)] ({x := t1} swap x0 x0 ({x := t2} swap z x0 t3))).
            *** apply aeq_m_subst_sub_neq; default_simp. repeat apply notin_union_3; default_simp. apply fv_nom_remove; default_simp.
            *** rewrite swap_id. apply aeq_sub_same.
              **** apply H. rewrite swap_size_eq. lia.
              **** apply H. lia.
          ** apply aeq_sym. apply aeq_m_subst_sub_neq. 
            *** assumption.
            *** apply notin_union_3; try apply fv_nom_remove; default_simp.
Qed. 

Lemma aeq_m_subst_out_neq: forall t1 t1' t2 x y, x <> y -> x `notin` (fv_nom t1') -> t1 =α (swap x y t1') -> ({x := t2}t1) =α ({y := t2}t1').
Proof. 
 intros t1 t1' t2 x y Hneq Hnotin Haeq. apply aeq_trans with ({x := t2} swap x y t1').
    - apply aeq_m_subst_out. assumption.
    - assert (Hnotin' := Hnotin). 
      assert (Haeq': t1' =α swap x y t1).
      {
        apply aeq_swap with x y. rewrite swap_involutive. apply aeq_sym. assumption.
      }
      apply aeq_fv_nom in Haeq'. rewrite Haeq' in Hnotin'. clear Haeq Haeq'.
      generalize dependent y. generalize dependent x. generalize dependent t2. generalize dependent t1.
      induction t1' as [ z | t1' z IH | t1' t1'' IH | t1' t1'' z IH] using n_sexp_size_induction.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. unfold vswap. destruct (z == x).
        * subst. apply notin_singleton_1 in Hnotin. contradiction.
        * destruct (z == y).
          ** subst. repeat rewrite m_subst_var_eq. apply aeq_refl.
          ** repeat rewrite m_subst_var_neq.
             *** apply aeq_refl.
             *** assumption.
             *** assumption.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
        * subst. unfold vswap. rewrite eq_dec_refl. apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) (Metatheory.union (singleton y) (singleton x)))))) in n_abs z ({y := t2} (swap x z t1'))).
          ** default_simp. assert (Hneq': x0 <> x). { repeat apply notin_union_2 in n. apply notin_singleton_1 in n. symmetry; assumption. }
             apply aeq_trans with (n_abs x0 ({x := t2}(swap y x0 (swap x y t1')))).
             *** apply aeq_m_subst_abs_neq.
                 **** assumption.
                 **** apply notin_union.
                      ***** apply notin_union_1 in n. assumption.
                      ***** apply notin_union.
                      ****** simpl. apply notin_remove_2. apply notin_fv_nom_swap_neq. 
                      ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. symmetry; assumption.
                      ******* assumption.
                      ******* apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ****** apply notin_singleton. symmetry; assumption.
             *** apply aeq_abs_same. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ x y). rewrite shuffle_swap.
                 **** rewrite (swap_symmetric _ x0 x). rewrite shuffle_swap.
                      ***** apply IH with t1.
                      ****** simpl. rewrite swap_size_eq. lia.
                      ****** apply notin_fv_nom_remove_swap_inc. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ****** assumption.
                      ****** assumption.
                      ***** assumption.
                      ***** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. symmetry; assumption. 
                 **** assumption.
                 **** symmetry; assumption.
          ** default_simp. apply aeq_sym. apply aeq_m_subst_abs_neq.
             *** symmetry; assumption.
             *** apply notin_union.
                 **** apply notin_union_1 in n. assumption.
                 **** apply notin_union.
                      ***** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ***** auto.
        * unfold vswap. destruct (z == x).
          ** subst.  apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) (Metatheory.union (singleton y) (singleton x)))))) in n_abs z ({y := t2} (swap x z t1'))).
          *** default_simp. assert (Hneq': x0 <> x). { repeat apply notin_union_2 in n. apply notin_singleton_1 in n. symmetry; assumption. }
             apply aeq_trans with (n_abs x0 ({x := t2}(swap y x0 (swap x y t1')))).
             **** apply aeq_m_subst_abs_neq.
                 ***** assumption.
                 ***** apply notin_union.
                      ****** apply notin_union_1 in n. assumption.
                      ****** apply notin_union.
                      ******* simpl. apply notin_remove_2. apply notin_fv_nom_swap_neq. 
                      ******** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. symmetry; assumption.
                      ******** assumption.
                      ******** apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ******* apply notin_singleton. symmetry; assumption.
             **** apply aeq_abs_same. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ x y). rewrite shuffle_swap.
                 ***** rewrite (swap_symmetric _ x0 x). rewrite shuffle_swap.
                      ****** apply IH with t1.
                      ******* simpl. rewrite swap_size_eq. lia.
                      ******* apply notin_fv_nom_remove_swap_inc. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ******* assumption.
                      ******* assumption.
                      ****** assumption.
                      ****** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. symmetry; assumption. 
                 ***** assumption.
                 ***** symmetry; assumption.
          *** default_simp. apply aeq_sym. apply aeq_m_subst_abs_neq.
             **** symmetry; assumption.
             **** apply notin_union.
                 ***** apply notin_union_1 in n. assumption.
                 ***** apply notin_union.
                      ****** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ****** auto.
          ** destruct (z == y).
            *** subst. repeat rewrite m_subst_abs_eq. apply aeq_abs_diff; try assumption. rewrite swap_symmetric. apply aeq_refl.
            *** apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) (Metatheory.union (singleton y) (singleton x)))))) in n_abs z0 ({y := t2} (swap z z0 t1'))).
              **** default_simp. apply aeq_trans with (n_abs x0 ({x := t2} swap z x0 (swap x y t1'))).
                ***** apply aeq_m_subst_abs_neq.
                  ****** symmetry; assumption.
                  ****** repeat apply notin_union.
                  ******* apply notin_union_1 in n1. assumption.
                  ******* simpl. apply notin_remove_2. apply notin_fv_nom_swap_neq.
                  ******** apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_singleton_1 in n1. symmetry; assumption. 
                  ******** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. symmetry; assumption.
                  ******** apply notin_union_2 in n1. apply notin_union_1 in n1. assumption. 
                  ******* repeat apply notin_union_2 in n1. assumption.
                ***** apply aeq_abs_same. rewrite swap_symmetric_2; try auto. apply IH with t1.
                  ****** simpl. rewrite swap_size_eq. lia.
                  ****** apply notin_fv_nom_swap_neq; auto.
                  ****** assumption.
                  ****** assumption. 
              **** default_simp. apply aeq_sym. apply aeq_m_subst_abs_neq. 
                ***** symmetry; assumption. 
                ***** apply notin_union. 
                ****** apply notin_union_1 in n1. assumption.
                ****** apply notin_union.
                ******* simpl. apply notin_remove_2. apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
                ******* apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. repeat rewrite m_subst_app. apply aeq_app.
        * apply IH with t1.
          ** lia.
          ** apply notin_union_1 in Hnotin. assumption.
          ** assumption.
          ** assumption.
        * apply IH with t1. 
          ** lia.
          ** apply notin_union_2 in Hnotin. assumption.
          ** assumption.
          ** assumption.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. unfold vswap. destruct (z == x).
        * apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) 
          (Metatheory.union (fv_nom t1'') (Metatheory.union (singleton y) (singleton x))))))) in ([z := {x := t2} swap x y t1''] ({x := t2} swap y z (swap x y t1')))).
          ** destruct (atom_fresh (union (fv_nom t2) (union (fv_nom t1') (union (fv_nom (swap x y t1)) (union (fv_nom t1'') (union (singleton y) (singleton x))))))).  
             apply aeq_m_subst_sub_neq.
            *** assumption.
            *** apply notin_union.
              **** apply notin_union_1 in n. assumption.
              **** apply notin_union.
              ***** simpl. apply notin_union.
              ****** apply notin_remove_2. apply notin_fv_nom_swap_neq.
              ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. symmetry; assumption.
              ******* repeat apply notin_union_2 in n. apply notin_singleton_1 in n. symmetry; assumption.
              ******* apply notin_union_2 in n. apply notin_union_1 in n. assumption.
              ****** apply notin_fv_nom_swap_neq.
              ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n.  apply notin_union_2 in n.  apply notin_union_1 in n. apply notin_singleton_1 in n. symmetry; assumption. 
              ******* repeat apply notin_union_2 in n. apply notin_singleton_1 in n. symmetry; assumption.
              ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.  
              ***** repeat apply notin_union_2 in n. assumption.
          ** default_simp. pose proof aeq_m_subst_sub_neq. specialize (H t1' t1'' t2 y x x0). apply aeq_trans with ([x0 := {y := t2} t1''] ({y := t2} swap x x0 t1')).
            *** apply aeq_sub_same.
              **** rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ x y). rewrite shuffle_swap; auto.
                   rewrite swap_symmetric. rewrite shuffle_swap; auto. apply IH with t1. 
                ***** simpl. rewrite swap_size_eq. lia.
                ***** apply notin_fv_nom_remove_swap_inc; auto. 
                ***** assumption.
                ***** assumption.
              **** apply IH with t1; auto. lia.
            *** apply aeq_sym. apply aeq_m_subst_sub_neq.
              **** symmetry; assumption.
              **** apply notin_union.
                ***** apply notin_union_1 in n. assumption.
                ***** apply notin_union.
                ****** simpl. apply notin_union.
                ******* apply notin_union_2 in n. apply notin_union_1 in n. apply notin_remove_2. assumption.
                ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                ****** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption. 
        * destruct (z == y).
          ** subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_diff.
            *** apply IH with t1.
              **** lia.
              **** apply notin_union_2 in Hnotin. assumption.
              **** assumption.
              **** assumption.
            *** assumption.
            *** apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin.
              **** contradiction.
              **** assumption.
            *** rewrite swap_symmetric. apply aeq_refl.
          ** apply aeq_trans with (let (z',_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (singleton z)
          (Metatheory.union (fv_nom t1'') (Metatheory.union (singleton y) (singleton x))))))) in ([z' := {x := t2} swap x y t1''] ({x := t2} swap z z' (swap x y t1')))).
            *** destruct (atom_fresh (union (fv_nom t2) (union (fv_nom t1')
           (union (singleton z) (union (fv_nom t1'') (union (singleton y) (singleton x))))))). apply aeq_m_subst_sub_neq.
              **** symmetry; assumption.
              **** apply notin_union.
              ***** apply notin_union_1 in n1. assumption.
              ***** apply notin_union.
              ****** simpl. apply notin_union.
              ******* apply notin_remove_2. apply notin_fv_nom_swap_neq; auto.
              ******* apply notin_fv_nom_swap_neq; auto.
              ****** repeat apply notin_union_2 in n1. assumption.
            *** default_simp. apply aeq_trans with ([x0 := {y := t2} t1''] ({y := t2} swap z x0 t1')).
              **** apply aeq_sub_same.
                ***** rewrite swap_symmetric_2; auto. apply IH with t1.
                  ****** rewrite swap_size_eq. lia.
                  ****** apply notin_fv_nom_swap_neq; auto.
                  ****** assumption.
                  ****** assumption.
                ***** apply IH with t1.
                  ****** lia.
                  ****** apply notin_union_2 in Hnotin. assumption.
                  ****** assumption.
                  ****** apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin.
                  ******* subst. contradiction.
                  ******* assumption.
              **** apply aeq_sym. apply aeq_m_subst_sub_neq.
                ***** symmetry; assumption.
                ***** apply notin_union.
                ****** apply notin_union_1 in n1. assumption.
                ****** apply notin_union; auto.
Qed.

Corollary aeq_m_subst_neq: forall t1 t1' t2 t2' x y, t2 =α t2' -> x <> y -> x `notin` fv_nom t1' -> t1 =α (swap x y t1') -> ({x := t2}t1) =α ({y := t2'}t1').
Proof.
  intros t1 t1' t2 t2' x y Haeq Hneq Hnotin Haeq'. apply aeq_trans with ({y := t2} t1').
  - apply aeq_m_subst_out_neq; assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

Lemma m_subst_lemma: forall t1 t2 t3 x y, x <> y -> x `notin` (fv_nom t3) ->
                     ({y := t3}({x := t2}t1)) =α ({x := ({y := t3}t2)}({y := t3}t1)).
Proof.
  induction t1 as  [z | t11 z | t11 t12 | t11 t12 z] using n_sexp_induction. 
- intros t2 t3 x y Hneq Hfv. case (x == z).
  + intro Heq. subst. rewrite m_subst_var_eq. case (y == z).
      * intro Heq. subst. contradiction.
      * intro Hneq'. rewrite m_subst_var_neq.
        ** rewrite m_subst_var_eq. apply aeq_refl.
        ** assumption.
  + intro Hneq'. case (x == z).
      * intro Heq. subst. contradiction.
      * intro Hneq''. rewrite m_subst_var_neq.
        ** case (y == z). 
           *** intro Heq. subst. rewrite m_subst_var_eq. apply aeq_sym. apply aeq_m_subst_notin. assumption.
           *** intro Hneq'''. repeat rewrite m_subst_var_neq.
               **** apply aeq_refl.
               **** symmetry. assumption.
               **** symmetry. assumption.
        ** symmetry. assumption.
- intros t2 t3 x y Hneq Hfv. case (z == x). 
    + intro Heq. subst. rewrite m_subst_abs_eq. apply aeq_sym. apply aeq_m_subst_notin. apply fv_nom_remove. 
        * assumption.
        * apply notin_remove_2. simpl. apply notin_remove_3. reflexivity.
    + intro Hneq'. destruct (y == z). 
      * subst. rewrite m_subst_abs_eq. pose proof aeq_m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom (n_abs z t11)) (singleton x)))). specialize (Habs t11 t2 x z w). apply aeq_trans with ({z := t3} n_abs w ({x := t2} swap z w t11)). 
        ** apply aeq_m_subst_out. apply Habs. 
           *** assumption.
           *** apply notin_union_2 in Fr. assumption.
        ** destruct (z == w). 
           *** subst. rewrite swap_id. rewrite m_subst_abs_eq. pose proof aeq_m_subst_abs_neq as H'. specialize (H' t11 ({w := t3}t2) x w w). rewrite swap_id in H'. rewrite H'.
               **** apply aeq_abs_same. assert (Fr' := Fr). apply notin_union_2 in Fr'. apply notin_union_1 in Fr'. apply aeq_m_subst_in. apply aeq_sym. apply aeq_m_subst_notin. assumption.
               **** assumption.
               **** apply notin_union.
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_remove_3. reflexivity.
                    ***** apply notin_union.
                    ****** simpl. apply notin_remove_3. reflexivity.
                    ****** apply notin_singleton. assumption.
           *** pose proof aeq_m_subst_abs_neq as Habs'. specialize (Habs' t11 ({z := t3}t2) x z w). rewrite Habs'. 
               **** pose proof aeq_m_subst_abs_neq as H'. specialize (H' ({x := t2} swap z w t11) t3 z w w). rewrite swap_id in H'. rewrite H'.
                    ***** apply aeq_abs_same. apply aeq_trans with ({x := {z := t3} t2}({z := t3}(swap z w t11))).
                    ****** apply H.
                    ******* reflexivity.
                    ******* assumption.
                    ******* assumption.
                    ****** apply aeq_m_subst_out. apply aeq_m_subst_notin. apply notin_fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_remove_1 in Fr. destruct Fr.
                    ******* contradiction.
                    ******* assumption.
                    ***** assumption.
                    *****  apply notin_union.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_union.
                    ******* simpl. apply notin_remove_3. reflexivity.
                    ******* apply notin_singleton. assumption.
               **** symmetry. assumption.
               **** apply notin_union.
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption. 
                    ***** apply notin_union.
                    ****** simpl. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr.  apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ******* assumption.
                    ******* apply not_eq_sym. assumption.
                    ****** apply notin_singleton. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.          
      * pose proof aeq_m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom (n_abs z t11)) (union (singleton x) (singleton y))))). specialize (Habs t11 t2 x z w). apply aeq_trans with ({y := t3} n_abs w ({x := t2} swap z w t11)). 
        *** apply aeq_m_subst_out. apply Habs.
            **** symmetry. assumption.
            **** apply notin_union_2 in Fr. pose proof AtomSetProperties.union_assoc as H'. specialize (H' (fv_nom (n_abs z t11)) (singleton x) (singleton y)). rewrite <- H' in Fr. rewrite <- AtomSetProperties.union_assoc in Fr. apply notin_union_1 in Fr. assumption.
        *** pose proof aeq_m_subst_abs_neq as Habs'. specialize (Habs' ({x := t2} swap z w t11) t3 y w w). rewrite swap_id in Habs'. rewrite Habs'. 
        **** pose proof aeq_m_subst_abs_neq as Habs''. specialize (Habs'' t11 t3 y z w). apply aeq_trans with ({x := {y := t3} t2} (n_abs w ({y := t3} swap z w t11))).
        ***** pose proof aeq_m_subst_abs_neq as Habs'''. specialize (Habs''' ({y := t3} swap z w t11) ({y := t3} t2) x w w). rewrite swap_id in Habs'''. rewrite Habs'''. 
        ****** apply aeq_abs_same. apply H.
        ******* reflexivity.
        ******* assumption.
        ******* assumption.
        ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
        ****** apply notin_union.
        ******* apply fv_nom_remove.
        ******** apply notin_union_1 in Fr. assumption.
        ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_remove_2. assumption.
        ******* apply notin_union.
        ******** simpl. apply notin_remove_3. reflexivity.
        ******** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ***** apply aeq_m_subst_out. apply aeq_sym. apply Habs''.
        ****** assumption.
        ****** apply notin_union.
        ******* apply notin_union_1 in Fr. assumption.
        ******* apply notin_union.
        ******** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ******** repeat apply notin_union_2 in Fr. assumption. 
        **** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
        **** apply notin_union.
        ***** apply notin_union_1 in Fr. assumption.
        ***** apply notin_union.
        ****** simpl. apply notin_remove_3. reflexivity.
        ****** repeat apply notin_union_2 in Fr. assumption. 
- intros t2 t3 x y Hneq Hfv. repeat rewrite m_subst_app. apply aeq_app. 
  + apply IHt12; assumption.
  + apply IHt1_1; assumption.
- intros t2 t3 x y Hneq Hfv. case (z == x).
  + intro Heq. subst. rewrite m_subst_sub_eq. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([x := t12]t11)) (singleton y)))). pose proof aeq_m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t3 y x w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap x w t11))).
    * case (x == w). 
      ** intro Heq. subst. rewrite m_subst_sub_eq. rewrite swap_id. pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 ({w := t2} t12) t3 y w w). rewrite Hsubneq'. 
         *** apply aeq_sub_same. 
             **** rewrite swap_id. apply aeq_refl. 
             **** apply IHt1_1; assumption. 
         *** symmetry. assumption.
         *** apply notin_union.
             **** apply notin_union_1 in Fr. assumption.
             **** apply notin_union.
                  ***** simpl. apply notin_union.
                  ****** apply notin_remove_3. reflexivity.
                  ****** apply fv_nom_remove.
                  *******  apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******* apply notin_remove_3. reflexivity.
                  ***** repeat apply notin_union_2 in Fr. assumption.
      ** intro Hneq'. pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({y := t3} swap x w t11) ({y := t3} t12) ({y := t3} t2) x w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'. 
         *** pose proof aeq_m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' t11 ({x := t2} t12) t3 y x w). rewrite Hsubneq''.
             **** apply aeq_sub_same. 
                  ***** apply aeq_sym. apply aeq_m_subst_notin. apply fv_nom_remove.
                  ******* assumption.
                  ******* apply notin_remove_2. apply notin_fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******** contradiction.
                  ******** assumption.
             ***** apply IHt1_1; assumption. 
         **** symmetry. assumption.
         **** apply notin_union.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_union.
                  ****** simpl. apply notin_union.
                  ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******** contradiction.
                  ******** assumption.
                  ******* apply fv_nom_remove.
                  ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ****** repeat apply notin_union_2 in Fr. assumption.
         *** assumption.
         *** apply notin_union.
             **** apply fv_nom_remove.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  **** apply notin_union.
                       ***** simpl. apply notin_union.
                       ****** apply notin_remove_3. reflexivity.
                       ****** apply fv_nom_remove.
                       ******* apply notin_union_1 in Fr. assumption.
                       ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                       ***** apply notin_singleton. assumption.
    * apply aeq_m_subst_out. rewrite Hsubneq.                 
      ** apply aeq_sub_same.
         *** apply aeq_refl.
         *** apply aeq_refl.
      ** symmetry. assumption.
      ** apply notin_union.
         *** apply notin_union_1 in Fr. assumption.
         *** apply notin_union.
             **** simpl. apply notin_union.
                  ***** case (w == x).
                  ****** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ****** intro Hneq'. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* symmetry in H0. contradiction.
                  ******* assumption.
                  ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
             **** repeat apply notin_union_2 in Fr. assumption.
  + intro Hneq'. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([z := t12]t11)) (union (singleton x) (singleton y))))). pose proof aeq_m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t2 x z w). apply aeq_trans with ({y := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))).
    * apply aeq_m_subst_out. pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 t12 t2 x z w). rewrite Hsubneq'.
      ** apply aeq_refl.
      ** symmetry. assumption.
      ** apply notin_union.
         *** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
         *** apply notin_union.
             **** simpl. apply notin_union.
                  ***** case (w == z).
                  ****** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ****** intro Hneq''. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* symmetry in H0. contradiction.
                  ******* assumption.
                  ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
             **** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
    * case (y == z). 
      ** intro Heq. subst. rewrite m_subst_sub_eq. pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({x := t2} swap z w t11) ({x := t2} t12) t3 z w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'.
         *** pose proof aeq_m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' t11 ({z := t3} t12) ({z := t3} t2) x z w). rewrite Hsubneq''.
             **** apply aeq_sub_same.
                  ***** apply aeq_trans with ({x := {z := t3} t2} ({z := t3}(swap z w t11))).
                  ****** apply H.
                  ******* reflexivity.
                  ******* assumption.
                  ******* assumption.
                  ****** apply aeq_m_subst_out. apply aeq_m_subst_notin. apply notin_fv_nom_swap. pose proof Fr as Fr'. repeat apply notin_union_2 in Fr'. apply notin_singleton_1 in Fr'. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* contradiction.
                  ******* assumption.
                  ***** apply IHt1_1; assumption.
                  **** assumption.
                  **** apply notin_union.
                       ***** apply fv_nom_remove.
                       ****** apply notin_union_1 in Fr. assumption.
                       ******  apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                       ***** apply notin_union.
                       ****** simpl. apply notin_union.
                       ******* pose proof Fr as Fr'. repeat apply notin_union_2 in Fr'. apply notin_singleton_1 in Fr'. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                       ******** contradiction.
                       ******** apply notin_remove_2. assumption.
                       ******* apply fv_nom_remove.
                       ******** apply notin_union_1 in Fr. assumption.
                       ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                       ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
         *** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
         *** apply notin_union.
             **** apply notin_union_1 in Fr. assumption.
             **** apply notin_union.
                  ***** simpl. apply notin_union.
                  ****** apply notin_remove_3. reflexivity.
                  ****** apply fv_nom_remove.
                  ******* apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ***** repeat apply notin_union_2 in Fr. assumption.                
      ** intro Hneq''. pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 t12 t3 y z w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap z w t11))).
         ***  pose proof aeq_m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' ({x := t2} swap z w t11) ({x := t2} t12) t3 y w w). rewrite swap_id in Hsubneq''. rewrite Hsubneq''.
              **** pose proof aeq_m_subst_sub_neq as Hsubneq'''. specialize (Hsubneq''' ({y := t3} swap z w t11) ({y := t3} t12) ({y := t3} t2) x w w). rewrite swap_id in Hsubneq'''. rewrite Hsubneq'''.
                   ***** apply aeq_sub_same.
                   ****** apply H.
                   ******* reflexivity.
                   ******* assumption.
                   ******* assumption.
                   ****** apply IHt1_1.
                   ******* assumption.
                   ******* assumption.
                   ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                   ***** apply notin_union.
                   ****** apply fv_nom_remove.
                   ******* apply notin_union_1 in Fr. assumption.
                   ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                   ****** apply notin_union.
                   ******* simpl. apply notin_union.
                   ******** apply notin_remove_3. reflexivity.
                   ******** apply fv_nom_remove.
                   ********* apply notin_union_1 in Fr. assumption.
                   ********* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                   ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.                 
                   **** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
                   **** apply notin_union.
                        ***** apply notin_union_1 in Fr. assumption.
                        ***** apply notin_union.
                        ****** simpl. apply notin_union.
                        ******* apply notin_remove_3. reflexivity.
                        ******* apply fv_nom_remove.
                        ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                        ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                        ****** repeat apply notin_union_2 in Fr. assumption.
         *** apply aeq_m_subst_out. apply aeq_sym. apply Hsubneq'.
             **** assumption.
             **** apply notin_union.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_union.
                  ****** simpl. apply notin_union.
                  ******* case (w == z).
                  ******** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ******** intro Hneq'''. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ********* symmetry in H0. contradiction.
                  ********* apply notin_remove_2. assumption.
                  ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ****** repeat apply notin_union_2 in Fr. assumption.
Qed.
(* end hide*)
