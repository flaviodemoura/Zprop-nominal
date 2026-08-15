(* Infrastructure *)
(* begin hide *)
Require Export Arith Lia.  
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Require Import Recdef.

Require Import infra_nom.
Require Import aeq_equiv_es.
(* end hide *)

(** * The metasubstitution operation of the $\lambda$-calculus *)

(** As presented in Section 2, the main operation of the $\lambda$-calculus is the $\beta$-reduction %(\ref{lambda:beta})% that expresses how to evaluate a function applied to an argument. The $\beta$-contractum $\metasub{t}{x}{u}$ represents a capture free in the sense that no free variable becomes bound by the application of the metasubstitution. This operation is in the meta level because it is outside the grammar of the $\lambda$-calculus (and hence its name). In %\cite{barendregtLambdaCalculusIts1984a}%, Barendregt defines it as follows:

%\vspace{.5cm}%
$\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_y.(\metasub{t_1}{x}{u}), & \mbox{ if } t = \lambda_y.t_1.
 \end{array}\right.$ %\vspace{.5cm}%

%\noindent% where it is assumed the so called "Barendregt's variable convention":

%\begin{tcolorbox}
 If $t_1, t_2, \ldots, t_n$ occur in a certain mathematical context (e.g. definition, proof), then in these terms all bound variables are chosen to be different from the free variables.  
\end{tcolorbox}%

This means that we are assumming that both $x \neq y$ and $y\notin fv(u)$ in the case $t = \lambda_y.t_1$. This approach is very convenient in informal proofs because it avoids having to rename bound variables. In order to formalize the capture free substitution, %{\it i.e.}% the metasubstitution, there are different possible approaches. In our case, we perform a renaming of bound variables whenever the metasubstitution is propagated inside a binder. In our case, there are two binders: abstractions and explicit substitutions.

Let $t$ and $u$ be terms, and $x$ a variable. The result of substituting $u$ for the free ocurrences of $x$ in $t$, written $\metasub{t}{x}{u}$ is defined as follows:%\newline%
%\begin{equation}\label{msubst}
\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y\ (x \neq y); \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_x.t_1, & \mbox{ if } t = \lambda_x.t_1; \\
  \lambda_z.(\metasub{(\swap{y}{z}{t_1})}{x}{u}), & \mbox{ if } t = \lambda_y.t_1, x \neq y \\ & \mbox{ and } \\ & z\notin fv(t\ u) \cup \{x\}; \\
  \esub{t_1}{x}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{x}{t_2}; \\
  \esub{\metasub{(\swap{y}{z}{t_1})}{x}{u}}{z}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{y}{t_2}, x \neq y \\ & \mbox{ and } \\ & z\notin fv(t\ u) \cup \{x\}.
 \end{array}\right.
\end{equation}%

%\noindent% and the corresponding Coq code is as follows: *)

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
(* begin hide *)
Definition m_subst (u : n_sexp) (x:atom) (t:n_sexp) :=
  subst_rec_fun t u x.
Notation "{ x := u } t" := (m_subst u x t) (at level 60).
(* end hide *)

(** Note that this function is not structurally recursive due to the swaps in the recursive calls, and that's why we need to provide the size of the term $t$ as the measure parameter. Alternatively, a structurally recursive version of the function [subst_rec_fun] can be found in the file [nominal.v] of the [Metalib] library%\footnote{\url{https://github.com/plclub/metalib}}%. It has the size of the term as an explicit parameter in which the substitution will be performed, and hence one has to deal with the size of the term in each recursive call. We write [{x:=u}t] instead of [subst_rec_fun t u x], and refer to it just as "metasubstitution".*)

(* begin hide *)
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

(* Require Import Setoid Morphisms. *)
(* end hide *)

(** The following lemma states that if $x \notin fv(t)$ then $\metasub{t}{x}{u} =_\alpha t$. In informal proofs the conclusion of this lemma is usually stated as a syntactic equality, %{\i.e.}% $\metasub{t}{x}{u} = t$ instead of the $\alpha$-equivalence, but the function [subst_rec_fun] renames bound variables whenever the metasubstitution is propagated inside an abstraction or an explicit substitution, even in the case that the metasubstitution has no effect in the subterm it is propagated, as long as the variables of the metasubstitution and the binder (abstraction or explicit substitution) are different of each other. That's why the syntactic equality does not hold here. *)

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
(** %\noindent{\bf Proof.}% The proof is done by induction on the size of the term [t] using [n_sexp_induction] defined above. The interesting cases are the abstraction and the explicit substituion. We focus in the abstraction case, %{\it i.e.}% when $t = \lambda_y.t_1$, where the goal to be proven is $\metasub{(\lambda_y.t_1)}{x}{u} =_\alpha \lambda_y.t_1$. We consider two cases: %\begin{enumerate} \item If $x = y$ the result is trivial because both LHS and RHS are equal to $\lambda_y.t_1$ \item If $x \neq y$ , we have to prove that $\lambda_z. \metasub{\swap{y}{z}{t_1}}{x}{u} =_{\alpha} \lambda_y. t_1$, where $z$ is a fresh name not in the set $fv\_nom(u)\cup fv\_nom(\lambda_y.t_1)\cup \{x\}$. The induction hypothesis express the fact that every term with the same size as the body $t_1$ of the abstraction  satisfies the property to be proven: $\forall t', |t'| = |t_1| \to \forall u\ x'\ x_0\ y_0, x' \notin fv(\swap{x_0}{y_0}{t'}) \to \metasub{(\swap{x_0}{y_0}{t'})}{x'}{u} =_\alpha \swap{x}{y}{t'}$. Therefore, according to the definition of the metasubstitution (function [subst_rec_fun]), the variable $y$ will be renamed to $z$, and the metasubstitution is propagated inside the abstraction resulting in the following goal: $\lambda_z.\metasub{(\swap{z}{y}{t_1})}{x}{u} =_\alpha \lambda_y.t_1$. Since $z \notin fv\_nom(\lambda_y.t_1) = fv\_nom(t_1)\backslash \{y\}$, there are two cases to consider, either $z = y$ or $z \in fv(t_1)$:
\begin{enumerate}
 \item $z = y$: In this case, we are done by the induction hypothesis taking $x_0=y_0=y$, for instance.
 \item $z \neq y$: In this case, we can apply the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$, resulting in the goal $\metasub{(\swap{y}{z}{t_1})}{x}{u} =_\alpha \swap{y}{z}{t_1}$ which holds by the induction hypothesis, since $|\swap{z}{y}{t_1}| = |t_1|$ and $x \notin fv\_nom(\swap{y}{z}{t_1})$ because $x \neq z$, $x \neq y$ and $x \notin fv\_nom(t_1)$.
\end{enumerate}
\end{enumerate}%

The explicit substitution case is also interesting, %{\it i.e.}% if $t = \esub{t_1}{y}{t_2}$, but it follows a similar strategy used in the abstraction case for $t_1$. For $t_2$ the result follows from the induction hypothesis. $\hfill\Box$*)

(* begin hide *)
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
(* end hide *)

(** The following lemmas concern the expected behaviour of the metasubstitution when the metasubstitution's variable is equal to the abstraction's variable. Their proofs are straightforward from the definition [subst_rec_fun]. The corresponding version when the metasubstitution's variable is different from the abstraction's variable will be presented later. %\newline%*)

Lemma m_subst_abs_eq: forall u x t, {x := u}(n_abs x t) = n_abs x t.
Proof.
  intros u x t. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_sub_eq: forall u x t1 t2, {x := u}(n_sub t1 x t2) = n_sub t1 x ({x := u}t2).
Proof.
  intros u x t1 t2. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

(* begin hide *)
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
(* end hide*)
                 
(* The problem is that we cannot rewrite $\alpha$-equalities inside metasubstitution unless we prove some special lemmas stating the compatibilities between them using the [Equations] library or something similar. We will present a solution that do not use any additional library, but it adds the following axiom to the formalization:

 Axiom Eq_implies_equality: forall s s': atoms, s [=] s' -> s = s'.

This axiom transforms a set equality into a syntactic equality. This will allow us to rewrite sets of atoms in a more flexible way. To show how it works, we will start proving the lemma [aeq_m_subst_in] without the need of the lemma [swap_m_subst]:*)
(* begin hide *)
Axiom Eq_implies_equality: forall t1 t2, t1 =α t2 -> fv_nom t1 = fv_nom t2.
(* end hide *)

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
       
(* begin hide *)
Lemma aeq_sub_notin: forall t1 t1' t2 t2' x y, x <> y ->  n_sub t1 x t2 =α n_sub t1' y t2' -> x `notin` fv_nom t1'.
Proof.
  intros t1 t1' t2 t2' x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.
(* end hide *)

(** The next lemma, named [aeq_m_subst_out], benefits from the strategy used in the previous proof, but its proof is not straightforward.*)

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
  - intros t u x Haeq. (*  Initially, the goal is [({x := u} ([y := t2] t1)) =α ({x := u} t)], and according to the definition of $\alpha$-equivalence, there are 2 subcases.*) inversion Haeq; subst. (* %\newline {\bf 1.}% In the first subcase, [t = ([y := t2'] t1')] with [t1 =α t1'] and [t2 =α t2'].*)
    + case (x == y). (* As in the abstraction case, we start comparing [x] and [y].*)
      * intro Heq. subst. (* When [x = y], the proof is trivial because both metasubstitutions are removed by applying lemma [m_subst_sub_eq] twice, and we get the following goal: [([y := {y := u} t2] t1) =α ([y := {y := u} t2'] t1')]*) repeat rewrite m_subst_sub_eq. apply aeq_sub_same. (* We compare the corresponding components of the explicit substitution via the constructor [aeq_sub_same], and the first case is trivial since [t1 =α t1'].*)
        ** assumption.
        ** apply IHt1. assumption. (* In order to show that [({y := u} t2) =α ({y := u} t2')], we apply the induction hypothesis.*)
      * intro Hneq. (* When [x <> y], we propagate the metasubstitutions inside the explicit substitution on both sides.*) unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y).
        ** contradiction.
        ** pose proof H4 as Hfvt1. apply Eq_implies_equality in Hfvt1. pose proof H5 as Hfvt2. apply Eq_implies_equality in Hfvt2. simpl. rewrite Hfvt1. rewrite Hfvt2. destruct (atom_fresh (union (fv_nom u) (union (union (remove y (fv_nom t1')) (fv_nom t2')) (singleton x)))). (* As [t1 =α t1'] and [t2 =α t2'], we have that [fv_nom t1 = fv_nom t1'] and [fv_nom t2 = fv_nom t2'], and we need just one fresh name, say [x0], to do these propagations, as long as [x0] does not belong to the set $fv(u)\cup fv(\metasub{t_1'}{y}{t_2'})\cup \{x\}$. The goal after the propagation is [([x0 := {x := u}t2'] {x := u}(swap y x0 t1')) =α ([x0 := {x := u}t2] {x := u}(swap y x0 t1))], and we proceed by a componentwise comparison via constructor [aeq_sub_same].*) apply aeq_sub_same.
           *** apply H. (* Each subcase is proved by the induction hypothesis.*)
               **** apply aeq_size in H4. symmetry. assumption.
               **** apply aeq_swap. apply aeq_sym. assumption.
           *** apply aeq_sym. apply IHt1. assumption.
    + case (x == y). (* %\newline {\bf 2.}% In the second subcase, the goal is [({x := u} ([y := t2] t1)) =α ({x := u} ([y0 := t2'] t1'))] with [y <> y0]. We proceed by comparing [x] and [y].*)
      * intro Heq. subst. (* If [x = y] then the metasubstitution of the LHS only propagates to the subterm [t2].*) rewrite m_subst_sub_eq. case (y == y0). 
        ** intro Heq. subst. contradiction. 
        ** intro Hneq. (* In the RHS, the metasubstitution is propagated to both subterms because [x = y <> y0].*) unfold m_subst in *. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (y == y0).
           *** contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y0 := t2'] t1')) (singleton y)))). (* To do so, we take a fresh name [x] that is not in the set $fv(u) \cup fv(\esub{t_1'}{y_0}{t_2'})$. We proceed by comparing componentwise according to the constructor [aeq_sub_diff].*) apply aeq_sub_diff.
               **** apply aeq_sym. apply IHt1. assumption. (* The proof that [{y := u}t2 =α {y := u}t2'] is straightforward by the induction hypothesis.*)
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
               **** apply aeq_trans with (swap y0 x t1'). (* The proof that [{y := u}(swap y0 x t1') =α swap y x t1] is done by lemma [aeq_m_subst_notin] since [y <> y0], [y <> x] and [y] is not in $fv(t_1')$.*)
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
      * intro Hneq. (* When [x <> y], we start with the following goal: [({x := u} ([y := t2] t1)) =α ({x := u} ([y0 := t2'] t1'))]. We proceed by comparing [x] and [y0].*) case (x == y0).
        ** intro Heq. subst. (* When [x = y0], the strategy is similar to the previous case [x = y] and [x <> y0].*) rewrite m_subst_sub_eq. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y0 == y).
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
        ** intro Hneq'. (* The last case is when [x <> y] and [x <> y0]. The current goal is [({x := u} ([y := t2] t1)) =α ({x := u} ([y0 := t2'] t1'))].*) unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y).
           *** contradiction.
           *** apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y0).
               **** contradiction.
               ****  apply Eq_implies_equality in Haeq. simpl in *. rewrite Haeq. destruct (atom_fresh (union (fv_nom u) (union (union (remove y0 (fv_nom t1')) (fv_nom t2')) (singleton x)))). (* We take a fresh name [x0] that is not in the set $fv(u)\cup fv(\esub{t_1'}{y_0}{t_2'})\cup \{ x \}$, and propagate the metasubstitutions inside the explicit substitutions according to the definition of the metasubstitution. The current goal is [([x0 := {x := u}t2']({x := u}(swap y0 x0 t1'))) =a
  ([x0 := {x := u}t2]({x := u}(swap y x0 t1)))], and we proceed using the constructor [aeq_sub_same]. Each subcase is proved by the induction hypothesis. *) apply aeq_sub_same.
                    ***** apply H.
                    ****** apply aeq_size in H7. rewrite swap_size_eq in H7. symmetry. assumption.
                    ****** apply (aeq_swap _ _ y x0) in H7. rewrite H7. apply aeq_sym. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). case (x0 == y0).
                    ******* intro Heq. subst. rewrite (swap_symmetric _ y0 y). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ******* intro Hneq''. apply aeq_swap_swap.
                    ******** apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1. subst. contradiction.
                    ********* assumption.
                    ******** assumption.
                    ***** apply aeq_sym. apply IHt1. assumption.
Qed. (** %\noindent{\bf Proof.}% The proof is by induction on the size of the term [t]. Note that induction on the hypothesis [t =α t'] does not work due to a similar problem involving swaps that appears when structural induction on [t] is used. The abstraction and the explicit substitution are the interesting cases.

In the abstraction case, we need to prove that $\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{t'}{x}{u}$, where $\lambda_y. t_1 =_{\alpha} t'$ by hypothesis. Therefore, $t'$ must be an abstraction, and according to our definition of $\alpha$-equivalence there are two possible subcases: %\begin{enumerate} \item In the first subcase, $t' = \lambda_y.t_2$, where $t_1 =_{\alpha} t_2$, and hence the current goal is $\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{(\lambda_y.t_2)}{x}{u}$. We proceed by comparing $x$ and $y$:
\begin{enumerate}
 \item If $x = y$ then, we are done by using twice lemma $m\_subst\_abs\_eq$.
 \item When $x \neq y$, then we need to propagate the metasubstitution on both sides of the goal. On the LHS, we need a fresh name that is not in the set $fv(u)\cup fv(\lambda_y.t_1) \cup \{x\}$, while for the RHS, the fresh name cannot belong to the set $fv(u)\cup fv(\lambda_y.t_2) \cup \{x\}$. From the hypothesis $t_1 =_{\alpha} t_2$, we know, by lemma $aeq\_fv\_nom$, that the sets $fv\_nom(t_1)$ and  $fv\_nom(t_2)$ are equal. Therefore, we can take just one fresh name, say $z$, and propagate both metasubstitutions over abstractions with the same binding, and we conclude with the induction hypothesis.
\end{enumerate}
\item In the second subcase, $t' = \lambda_{y_0}.t_2$, where $t_1 =_{\alpha} \swap{y_0}{y}{t_2}$ and $y \neq y_0$. The current goal is $$\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{(\lambda_{y_0}.t_2)}{x}{u}$$ and we proceed by comparing $x$ and $y$:
\begin{enumerate}
 \item If $x = y$ then the goal simplifies to $\lambda_y.t_1 =_{\alpha} \metasub{(\lambda_{y_0}.t_2)}{x}{u}$ by lemma $m\_subst\_abs\_eq$, and we pick a fresh name $x$, that is not in the set $fv\_nom(u) \cup fv\_nom(\lambda_{y_0}.t_2) \cup \{y\}$, and propagate the metasubstitution on the RHS of the goal, resulting in the new goal $\lambda_y. t_1 =_{\alpha} \lambda_x.\metasub{(\swap{y_0}{x}{t_2})}{y}{u}$. Note that the metasubstitution on the RHS has no effect in the term $\swap{y_0}{x}{t_2}$ because $y \neq y_0$, $y \neq x$ and $y$ does not occur free in $t_2$ and we conclude by hypothesis.
\item If $x \neq y$ then we proceed by comparing $x$ and $y_0$ on the RHS, and the proof, when $x = y_0$, is analogous to the previous subcase. When both $x \neq y$ and $x \neq y_0$ then we need to propagate the metasubstitution on both sides of the goal $\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{(\lambda_{y_0}.t_2)}{x}{u}$. We have that $\lambda_y.t_1 =_{\alpha} \lambda_{y_0}.t_2$ and hence the sets $fv\_nom(\lambda_y.t_1)$ and $fv\_nom(\lambda_{y_0}.t_2)$ are equal. Therefore, only one fresh name, say $x_0$, that is not in the set $x_0 \notin fv\_nom(u) \cup fv\_nom(\lambda_{y_0}.t_2) \cup \{x\}$ is enough to fulfill the conditions for propagating the metasubstitutions on both sides of the goal, and we are done by the induction hypothesis.
\end{enumerate}
\item The explicit substitution operation is also interesting, but we will not comment because we are running out of space. $\hfill\Box$
\end{enumerate}%*)
   
(** As a corollary, one can join the lemmas [aeq_m_subst_in] and [aeq_m_subst_out] as follows:*)

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

(** Now, we show how to propagate a swap inside metasubstitutions using the decomposition of the metasubstitution provided by the corollary [aeq_m_subst_eq].%\newline% *)

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
    + intros x y Hneq z u. simpl. case (y' == z). (* The case of the explicit substitution follows a similar strategy of the abstraction. The initial goal is to prove that [swap x y ({z := u}(n_sub t1 y' t2)) =α {(vswap x y z) := (swap x y u)}(swap x y (n_sub t1 y' t2))] and we start comparing the variables [y'] and [z].*)
      * intro Heq. subst. repeat rewrite m_subst_sub_eq. simpl. apply aeq_sub_same. (* When [y' = z], the metasubstitution has no effect on the body of the metasubstitution but it can still be propagated to the term [t2]. Therefore, this case is proved using the induction hypothesis over [t2]. *)
        ** apply aeq_refl.
        ** apply IHt1. assumption.
      * intro Hneq'. unfold m_subst. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (vswap_neq x y) in n. contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y' t2)) (singleton z)))). destruct (atom_fresh (union (fv_nom (swap x y u)) (union (fv_nom (n_sub (swap x y t1) (vswap x y y') (swap x y t2))) (singleton (vswap x y z))))). simpl in *. apply aeq_sym. case (x1 == vswap x y x0). (* When [y' <> z], then the metasubstitutions are propagated on both sides of the $\alpha$-equation. Analogously to the abstraction case, one new name for each propagation is created. Let [x0] be a new name not in the set $fv(\esub{t1}{y'}{t2})\cup fv(u) \cup \{z\}$, and [x1], a new name not in the set $fv(\esub{\swap{x}{y}{t1}}{\vswap{x}{y}{y'}}{\swap{x}{y}{t2}})\cup fv(\swap{x}{y}{u}) \cup \{\vswap{x}{y}{z}\}$. After the propagation step, we have the goal [[(vswap x y x0) := (swap x y ({z := u}t2))](swap x y ({z := u}(swap y' x0 t1))) =a
  [x1 := ({(vswap x y z) := (swap x y u)}(swap x y t2))]({(vswap x y z) := (swap x y u)}(swap (vswap x y y') x1 (swap x y t1)))]. We proceed by comparing [x1] and [(swap x y x0)].*)
               **** intro Heq. subst. apply aeq_sub_same. (* If [x1 = vswap x y x0] then after an application of the rule [aeq_sub_same], we are done by the induction hypothesis for both the body and the argument of the explicit substitution.*)
                    ***** rewrite <- swap_equivariance. apply H.
                    ****** reflexivity.
                    ****** assumption.
                    ***** apply IHt1. assumption.
               **** intro Hneq''. apply aeq_sub_diff.
                    ***** apply IHt1. assumption. (* If [x1 <> vswap x y x0] then we apply the rule [aeq_sub_diff] to decompose the explicit substitution in its components. The second component is straightforward  by the induction hypothesis.*)
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
                    ***** unfold m_subst in *. rewrite H. (* The first component follows the strategy used in the abstraction case. The current goal, obtained after the application of the rule [aeq_sub_diff] is [swap x y ({z := u}(swap y' x0 t1)) =a
  swap x1 (vswap x y x0) ({(vswap x y z) := (swap x y u)}(swap (vswap x y y') x1 (swap x y t1)))]. The induction hypothesis is used twice to propagate the swap on both the LHS and RHS of the $\alpha$-equality. This swap has no effect on the variable [z] of the metasubstitution, therefore we can apply lemma [aeq_m_subst_eq], and each generated case is proved by routine manipulation of swaps. *)
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

(** The following two lemmas toghether with lemmas [m_subst_abs_eq] and [m_subst_sub_eq] are essential in simplifying the propagations of metasubstitution. They are presented here because they depend on lemma [aeq_swap_subst_rec_fun]. *)

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

(* In fact, the need of the lemma [aeq_swap_subst_rec_fun] in the proofs of the two previous lemmas is justified by the fact that when the $\alpha$-equation involves abstractions with different binders, or explicit substitutions with different binders, the rules [aeq_abs_diff] and [aeq_sub_diff] introduce swaps that are outside the metasubstitutions. *)

(* This is the intended behaviour of the metasubstitution *)
(* Lemma fv_nom_metasub: forall t u x,  x `notin` (fv_nom t) ->  fv_nom ({x := u}t) [=] fv_nom t.
Proof. 
  induction t.
  - intros u x' Hfv. simpl in *. apply notin_singleton_1 in Hfv. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x' == x).
    + subst. contradiction.
    + simpl. reflexivity.
  - intros u x' Hfv. simpl in *. case (x' == x).
    + intro Heq. subst. rewrite m_subst_abs_eq. simpl. reflexivity.
    + intro Hneq. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x' == x).
      * contradiction.
      * destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs x t)) (singleton x')))). simpl. case (x0 == x).
        ** intro Heq. subst. apply AtomSetProperties.Equal_remove. rewrite swap_id. apply IHt. apply notin_remove_1 in Hfv. destruct Hfv.
           *** symmetry in H. contradiction.
           *** assumption.
        ** intro Hneq'. apply notin_remove_1 in Hfv. destruct Hfv.
           *** symmetry in H. contradiction.
           *** apply (IHt u) in H. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
               **** symmetry in H0. contradiction.
               **** apply (IHt u) in H0. Admitted. *)             

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

(**
The next corollary stablishes the compatibility of the metasubstitution operation with $\alpha$-equivalence when the variables of the metasubstitutions are different: 
*)
Corollary aeq_m_subst_neq: forall t1 t1' t2 t2' x y, t2 =α t2' -> x <> y -> x `notin` fv_nom t1' -> t1 =α (swap x y t1') -> ({x := t2}t1) =α ({y := t2'}t1').
Proof.
  intros t1 t1' t2 t2' x y Haeq Hneq Hnotin Haeq'. apply aeq_trans with ({y := t2} t1').
  - apply aeq_m_subst_out_neq; assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

(* The substitution lemma *)

(** In the pure $\lambda$-calculus, the substitution lemma is probably the first non trivial property. In our framework, we have defined two different substitution operators, namely, the metasubstitution denoted by $\metasub{t}{x}{u}$ and the explicit substitution, written as $\esub{t}{x}{u}$. In what follows, we present the main steps of our proof of the substitution lemma for [n_sexp] terms, %{\it i.e.}% for nominal terms with explicit substitutions. *)

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
        ****** repeat apply notin_union_2 in Fr. assumption. (** %\noindent{\bf Proof.}% The proof is by induction on the size of [t1]. The interesting cases are the abstraction and the explicit substitution. We focus on the former, %{\it i.e.}% $t1= \lambda_z.t_1'$, whose initial goal is

$\metasub{(\metasub{(\lambda_z.t_1')}{x}{t_2})}{y}{t_3} =_{\alpha} \metasub{(\metasub{(\lambda_z .t_1')}{y}{t_3})}{x}{\metasub{t_2}{y}{t_3}}$

%\noindent% assuming that $x \neq y$ and $x \notin fv\_nom(t_3)$. The induction hypothesis generated by this case states that the lemma holds for any term of the size of $t_1'$, %{\it i.e.}% any term with the same size of the body of the abstraction. We start comparing $z$ with $x$ aiming to apply the definition of the metasubstitution on the LHS of the goal. %\begin{enumerate}
\item When $z = x$, the subterm $\metasub{\lambda_x.t_1'}{x}{t_2}$ reduces to $\lambda_x.t_1'$ by lemma $m\_subst\_abs\_eq$, and then the LHS reduces to $\metasub{\lambda_x.t_1'}{y}{t_3}$. The RHS $\metasub{\metasub{\lambda_x.t_1'}{y}{t_3}}{x}{\metasub{t_2}{y}{t_3}}$ also reduces to it because $x$ does not occur free neither in $\lambda_x.t_1'$ nor in $t_3$, and we are done.
\item When $z \neq x$, then we compare $y$ with $z$.
\begin{enumerate}
 \item When $y = z$, the subterm $\metasub{(\lambda_z.t_1')}{y}{t_3}$ can be simplified to $\lambda_z.t_1'$, by lemma $m\_subst\_abs\_eq$. On the LHS, we propagate the internal metasubstitution over the abstraction taking a fresh name $w$ not in the set $fv\_nom(\lambda_z.t_1') \cup fv\_nom(t_3) \cup fv\_nom(t_2) \cup \{x\}$, where the goal is $\metasub{(\lambda_w.(\metasub{\swap{z}{w}{t_1'}}{x}{t_2}))}{z}{t_3} =_{\alpha} \metasub{(\lambda_z.t_1')}{x}{\metasub{t_2}{z}{t_3}}$. We proceed by comparing $z$ and $w$: \begin{enumerate}
\item If $z = w$ then the current goal simplifies to

$\metasub{(\lambda_w.(\metasub{t_1'}{x}{t_2}))}{w}{t_3} =_{\alpha} \metasub{(\lambda_w.t_1')}{x}{\metasub{t_2}{w}{t_3}}$

We can propagate the metasubstitution on the RHS and there is no need for a fresh name since the variable $w$ fullfil the condition required by lemma $m\_subst\_abs\_neq$. We conclude with lemmas $aeq\_m\_subst\_in$ and $m\_subst\_notin$.
\item If $z \neq w$ then we can propagate the metasubstitutions on both sides of the goal taking $w$ as the fresh name that fullfil the conditions of lemma $m\_subst\_abs\_neq$. We proceed with $aeq\_abs\_same$, and conclude by the induction hypothesis.
\end{enumerate}
\item If $y \neq z$ then we follow a similar strategy that avoids unnecessary generation of fresh names. In this way, we take a fresh $w$ that is not in the set $fv\_nom(t_3)\cup fv\_nom(t_2)\cup fv\_nom(\lambda_z.t_1')\cup \{x\}\cup \{y\}$, and propagate the metasubstitution inside the abstraction resulting in the goal $\lambda_w. (\metasub{(\metasub{\swap{z}{w}{t_1'}}{x}{t_2})}{y}{t_3} =_{\alpha} \lambda_w. (\metasub{(\metasub{\swap{z}{w}{t_1'}}{y}{t_3})}{x}{\metasub{t_2}{y}{t_3}}$. We conclude by the induction hypothesis. $\hfill\Box$
\end{enumerate}
\end{enumerate}%*) 
- intros t2 t3 x y Hneq Hfv. repeat rewrite m_subst_app. apply aeq_app. 
  + apply IHt12; assumption.
  + apply IHt1_1; assumption.
- intros t2 t3 x y Hneq Hfv. (* In the explicit substitution case, the initial goal is [({y := t3} ({x := t2} ([z := t12] t11))) =α ({x := {y := t3} t2} ({y := t3} ([z := t12] t11)))], and we start comparing [x] and [z]. *) case (z == x).
  + intro Heq. subst. rewrite m_subst_sub_eq. (* When [z = x], the LHS [({y := t3} ({x := t2} ([z := t12] t11)))] reduces to [([x := {x := t2} t12] t11)], but differently to the abstraction case, the external metasubstitution of the RHS cannot be ignored because [x] may occur free in [t12], and it will therefore be propagated over the explicit substitution. We then need a fresh name, say [w], that is not in the set $fv(t_3)\cup fv(t_2) \cup fv(\esub{t_{11}}{x}{t_{12}}) \cup \{y\}$. We use lemma [aeq_m_subst_sub_neq] to perform the propagation.*) pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([x := t12]t11)) (singleton y)))). pose proof aeq_m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t3 y x w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap x w t11))).
    * case (x == w). (* We proceed by comparing [x] and [w] because if they are equal the external metasubstitution of the RHS can be removed as in the abstraction case.*)
      ** intro Heq. subst. rewrite m_subst_sub_eq. rewrite swap_id. pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 ({w := t2} t12) t3 y w w). rewrite Hsubneq'. (* The current goal is [({y := t3} ([w := {w := t2} t12] t11)) =α ([w := {w := {y := t3} t2} ({y := t3} t12)] ({y := t3} t11))], and the next step is to propagate the external metasubstitution of the LHS without the need of a new name.*)
         *** apply aeq_sub_same. (* As the same name [w] is used on both sides, we can proceed with [aeq_sub_same]. *)
             **** rewrite swap_id. apply aeq_refl. (* The first subcase is trivial.*)
             **** apply IHt1_1; assumption. (* And the second is proved by the induction hypothesis for [t12].*)
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
      ** intro Hneq'. (* When [x <> w], then we can propagate the external metasubstitutions on both sides of the current goal [({y := t3} ([x := {x := t2} t12] t11)) =α ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap x w t11)))]. We use two different instances of [aeq_m_subst_sub_neq], and on both cases we use the fresh name [w] that was already created.*) pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({y := t3} swap x w t11) ({y := t3} t12) ({y := t3} t2) x w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'. 
         *** pose proof aeq_m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' t11 ({x := t2} t12) t3 y x w). rewrite Hsubneq''.
             **** apply aeq_sub_same. (* Again, since we have used the same fresh name [w] on both sides of the $\alpha$-equation, we proceed with [aeq_sub_same].*)
                  ***** apply aeq_sym. apply aeq_m_subst_notin. (* In the first subcase, we need to prove that [({y := t3} swap x w t11) =α ({x := {y := t3} t2} ({y := t3} swap x w t11))], and we conclude with [aeq_m_subst_notin], since [x] does not occur free in [({y := t3} swap x w t11)].*) apply fv_nom_remove.
                  ******* assumption.
                  ******* apply notin_remove_2. apply notin_fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******** contradiction.
                  ******** assumption.
             ***** apply IHt1_1; assumption. (* The second subcase is proved by the induction hypothesis on [t12].*)
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
  + intro Hneq'. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([z := t12]t11)) (union (singleton x) (singleton y))))). (* When [z <> x], then we take a fresh name [w] such that it is not in the set $fv(t_3)\cup fv(t_2) \cup fv(\esub{t_{11}}{z}{t_{12}})\cup \{x\} \cup \{y\}$. The current goal is [({y := t3} ({x := t2} ([z := t12] t11))) =α ({x := {y := t3} t2} ({y := t3} ([z := t12] t11)))] and we start propagating the internal metasubstitution. Let's start with the LHS.*) pose proof aeq_m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t2 x z w). apply aeq_trans with ({y := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))).
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
    * case (y == z). (* After the propagation, we get the following goal [({y := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))) =α ({x := {y := t3} t2} ({y := t3} ([z := t12] t11)))]. We now compare [y] and [z], and propagate the internal metasubstitution of the RHS.*)
      ** intro Heq. subst. rewrite m_subst_sub_eq. (* When [y = z], we have the goal [({z := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))) =α ({x := {z := t3} t2} ([z := {z := t3} t12] t11))]. The next step is to propagate the external metasubstitutions on both sides of the current goal. To do so, we will use the same fresh name [w] on both propagations.*) pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({x := t2} swap z w t11) ({x := t2} t12) t3 z w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'.
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
      ** intro Hneq''. (* When [y <> z], we again propagate all the metasubstitutions, one in the LHS and two in the RHS, using the same fresh name [w] for all of them.*) pose proof aeq_m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 t12 t3 y z w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap z w t11))).
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

