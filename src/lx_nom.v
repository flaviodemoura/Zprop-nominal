(* begin hide *)
From Stdlib Require Export Arith Lia.
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Require Import infra_nom.
Require Import aeq_equiv_es.
Require Import msubst.
Require Import ZtoConfl_nom.

Lemma refltrans_m_subst1 (R: Rel n_sexp): forall t1 t2 t3 x, refltrans (ctx R) t1 t2 -> refltrans (ctx R) ({x := t1}t3) ({x := t2}t3).
Proof.
  intros t1 t2 t3 x H. induction t3 using n_sexp_size_induction.
    - destruct (x0 == x).
      + subst. repeat rewrite m_subst_var_eq. assumption.
      + repeat rewrite m_subst_var_neq.
        * apply refltrans_refl.
        * assumption.
        * assumption.
    - destruct (x == z).
      + subst. repeat rewrite m_subst_abs_eq. apply refltrans_n_abs. apply refltrans_refl.
      + apply refltrans_composition with (let (z',_) := (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) 
        (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t1) (fv_nom t2)))))) in (n_abs z' ({x := t1} swap z z' t3))).
          * default_simp. apply refl. apply aeq_m_subst_abs_neq; default_simp.
          * default_simp. pose proof aeq_m_subst_abs_neq. apply refltrans_composition with (n_abs x0 ({x := t2} swap z x0 t3)).
            ** apply refltrans_n_abs. apply H0. rewrite swap_size_eq. lia.
            ** apply refl. apply aeq_sym. apply aeq_m_subst_abs_neq; default_simp.
    - repeat rewrite m_subst_app. apply refltrans_n_app.
      + apply H0. simpl. lia.
      + apply H0. simpl. lia. 
    - destruct (x == z).
      * subst. repeat rewrite m_subst_sub_eq. apply refltrans_n_sub_in. apply H0. simpl. lia.
      * apply refltrans_composition with (let (z',_) := (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) 
        (Metatheory.union (fv_nom ([z := t3_2] t3_1)) (Metatheory.union (fv_nom t1) (fv_nom t2)))))) in ([z' := {x := t1} t3_2] ({x := t1} swap z z' t3_1))).
            *** default_simp. apply refl. apply aeq_m_subst_sub_neq; default_simp.
            *** default_simp. apply refltrans_composition with ([x0 := {x := t2} t3_2] ({x := t2} swap z x0 t3_1)).
              **** apply refltrans_n_sub.
                ***** apply H0. rewrite swap_size_eq. lia.
                ***** apply H0. lia. 
              **** apply refl. apply aeq_sym. apply aeq_m_subst_sub_neq; default_simp.
Qed.
(* end hide *)

(** * The $\lambda_x$ calculus with explicit substitutions *)

(** In this section, we formalize a version of the $\lambda_x$-calculus%\cite{linsNewFormulaExecution1986,linsPartialCategoricalMulticombinators1992,roseExplicitCyclicSubstitutions1992,blooPreservationStrongNormalisation1995}% in a nominal framework and prove its confluence via the compositional Z property%\cite{nakazawaCompositionalConfluenceProofs2016}%. This task can be seen as an application of our formalizations of the compositional Z property %\cite{fmm2021}% and the extension of the substitution lemma for calculi with explicit substitutions %\cite{limaFormalizedExtensionSubstitution2023}%.

As discussed in the introduction, calculi with explicit substitutions deconstruct the $\beta$-reduction into finer-grained steps, thereby functioning as an intermediary between the $\lambda$-calculus and its practical implementations. In the $\lambda_x$-calculus, the core idea is that $\beta$-reduction is divided into two parts, one that initiates the simulation of the $\beta$-step, and another that completes the simulation, as suggested by the following figure:

%\begin{tcolorbox}
$\centerline{\xymatrix{(\lambda_x.t_1)\ t_2 \ar@{->}[rr]_{\beta} & & \metasub{t_1}{x}{t_2} \\
    (\lambda_x.t_1)\ t_2 \ar@{->}[r]_{\tt b} & \esub{t_1}{x}{t_2} \ar@{->>}[r]_{\tt sc} & \metasub{t_1}{x}{t_2} \\}}$
\end{tcolorbox}
\noindent where the {\tt b}% step initiates the simulation of the $\beta$-reduction, and the %{\tt sc}% steps complete the simulation of the $\beta$-reduction, where the metasubstitution $\metasub{t_1}{x}{t_2}$ is extended to the explicit substitution as follows:

%\begin{equation}\label{msubst-es}
\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  t, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_x.t_1, & \mbox{ if } t = \lambda_x.t_1; \\
  \lambda_z.(\metasub{(\swap{y}{z}{t_1})}{x}{u}), & \mbox{ if } t = \lambda_y.t_1, x \neq y \\ & \mbox{ and } \\ & z\notin fv(t\ u) \cup \{x\}; \\
  \esub{t_1}{x}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{x}{t_2}; \\
  \esub{\metasub{(\swap{y}{z}{t_1})}{x}{u}}{z}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{y}{t_2}, \\ & x \neq y \mbox{ and } \\ & z\notin fv(t\ u) \cup \{x\}.
 \end{array}\right.
\end{equation}%

The %{\tt b}% step is inductively defined as the reduction that takes a $\beta$-redex , say $(\lambda_x\ t_1)\ t_2$ that is written as [(n_app  (n_abs x t1) t2)] in Rocq and reduces it to an explicit substitution:

*)

Inductive betax : Rel n_sexp :=
 | step_betax : forall (t1 t2: n_sexp) (x: atom),
     betax (n_app  (n_abs x t1) t2)  ([x:=t2]t1).

(**
%\noindent% then this reduction is done modulo $\alpha$-equivalence (cf. %\cite{limaFormalizedExtensionSubstitution2023}%).
*)
(* begin hide *)
Inductive betax_aeq: Rel n_sexp :=
| betax_aeq_step: forall t t' u u', t =α t' -> betax t' u' -> u' =α u -> betax_aeq t u.

(**

The contextual closure of the [beta_aeq] reduction is given by the following notation:

*)

Definition betax_ctx t u := ctx betax_aeq t u.
Notation "t →b u" := (betax_ctx t u) (at level 60).
Notation "t ↠b u" := (refltrans betax_ctx t u) (at level 60).
(* end hide *)
(** We write $\to_b$ for the contextual closure of the $b$-step modulo $\alpha$-equivalence, and $\to_{x}$ for the contextual closure of the reduction rules of the substitution calculus that are given below, where $x \neq y$:

%\begin{tcolorbox}
\begin{equation}\label{x:rules}
 \begin{array}{llll}
 \esub{y}{y}{t} & \to_{var} & t & \\
 \esub{x}{y}{t} & \to_{gc} & x & \\
 \esub{(\lambda_y.t_1)}{y}{t_2} & \to_{abs1} & \lambda_y.t_1 & \\
 \esub{(\lambda_x.t_1)}{y}{t_2} & \to_{abs2} & \lambda_x.(\esub{t_1}{y}{t_2}) & \mbox{, if } x \notin fv(t_2). \\
 \esub{(\lambda_x.t_1)}{y}{t_2} & \to_{abs3} & \lambda_z.(\esub{\swap{x}{z}{t_1}}{y}{t_2}) & \mbox{, where } z \mbox{ is fresh} \\ &&& \mbox{and } x \in fv(t_2). \\
 \esub{(t_1\ t_2)}{y}{t_3} & \to_{app} & (\esub{t_1}{y}{t_3})\ (\esub{t_2}{y}{t_3}) &
\end{array}
\end{equation}
\end{tcolorbox}%

The abstraction rule is formalized in three steps that capture the assumption that free variables cannot be captured. Therefore, in $abs1$ the term $t_1$ has no free occurrence of $y$ and the substitution $[y:= t_2]$ has no effect. In $abs2$, $t_1$ may have free occurrences of $y$ and the substitution is propagated inside the abstraction whose bound variable $x$ is not renamed because $x$ has no free occurrence in $t_2$. Finally, in $abs3$ a renaming by a fresh variable is mandatory since $x$ occurs free in $t_2$. Notice that %\cite{nakazawaCompositionalConfluenceProofs2016}% inherently handles $\alpha$-equivalence, requiring only one rule for abstraction: $\esub{(\lambda_x.t1)}{y}{t_2} \to \lambda_x.(\esub{t_1}{y}{t_2})$, i.e., it assumes that bound variables are renamed as needed to avoid capture of free variables.

In order to clarify the notation, we have that $\to_x = \to_{var} \cup \to_{gc}  \cup \to_{abs1} \cup \to_{abs2} \cup \to_{abs3} \cup \to_{app}$ and $\to_{lx} = \to_b \cup \to_x$. In addition, the two headed arrow $\tto_R$ denotes the reflexive transitive closure of the corresponding relation $R$.

Our goal is to prove that the $\lambda_x$-calculus is confluent, i.e., that the relation $\to_{lx}$ is confluent. To this end, we will show that the $\lambda_x$-calculus satisfies the compositional Z property, which is a sufficient condition for confluence. 
*)

(* begin hide *)
Inductive scx : Rel n_sexp :=
| step_var : forall (t: n_sexp) (y: atom),
    scx (n_sub (n_var y) y t) t
| step_gc : forall (t: n_sexp) (x y: atom),
    x <> y -> scx (n_sub (n_var x) y t) (n_var x)
| step_abs1 : forall (t1 t2: n_sexp) (y : atom),
    scx (n_sub (n_abs y t1) y t2)  (n_abs y t1)
| step_abs2 : forall (t1 t2: n_sexp) (x y: atom),
    x <> y -> x `notin` fv_nom t2 ->
    scx (n_sub (n_abs x t1) y t2)  (n_abs x (n_sub t1 y t2))
| step_abs3 : forall (t1 t2: n_sexp) (x y z: atom), x <> y -> z <> x -> z <> y ->
    x `in` fv_nom t2 -> z `notin` fv_nom t1 -> z `notin` fv_nom t2 ->
    scx (n_sub (n_abs x t1) y t2)  (n_abs z (n_sub (swap x z t1) y t2))
| step_app : forall (t1 t2 t3: n_sexp) (y: atom),
    scx (n_sub (n_app t1 t2) y t3) (n_app (n_sub t1 y t3) (n_sub t2 y t3)).

(**

Similarly to the rule [-->b], the contextual closure of the rules of the inductive definition [scx] modulo $\alpha$-equivalence is written as [-->x], and [-->lx] represents the union of [-->b] and [-->x].
 *)

Inductive scx_aeq: Rel n_sexp :=
| scx_aeq_step: forall t t' u u', t =α t' -> scx t' u' -> u' =α u -> scx_aeq t u.

Definition scx_ctx t u := ctx scx_aeq t u. 
Notation "t →x u" := (scx_ctx t u) (at level 60).
Notation "t ↠x u" := (refltrans scx_ctx t u) (at level 60).

Inductive lambdax: Rel n_sexp :=
| b_rule : forall t u, t →b u -> lambdax t u
| x_rule : forall t u, t →x u -> lambdax t u.

Notation "t →lx u" := (lambdax t u) (at level 60).
Notation "t ↠lx u" := (refltrans lambdax t u) (at level 60).

Lemma ctx_betax_beta_scx: forall t t', (t →lx t') <-> (t →b t' \/ t →x t'). 
Proof.
  intros t t'. split.
    - intro H. induction H.
      + left. assumption.
      + right. assumption.
    - intro H. destruct H.
      + apply b_rule. assumption.
      + apply x_rule. assumption.  
Qed.

Lemma refltrans_lx_b: forall t t', (t ↠b t') -> (t ↠lx t'). 
Proof.
  intros t t' H. induction H.
    - apply refl. assumption.
    - apply rtrans with t2.
      + apply b_rule. assumption.
      + assumption.
    - apply refltrans_composition with t2.
      + apply refl. assumption.
      + assumption.
Qed. 

Lemma refltrans_lx_x: forall t t', t ↠x t' -> (t ↠lx t'). 
Proof.
    intros t t' H. induction H.
    - apply refl. assumption.
    - apply rtrans with t2.
      + apply x_rule. assumption.
      + assumption.
    - apply refltrans_composition with t2.
      + apply refl. assumption.
      + assumption.
Qed.

Lemma refltrans_n_abs_lx: forall t1 t2 x, t1 ↠lx t2 -> n_abs x t1 ↠lx n_abs x t2.
Proof.
  intros t1 t2 x H. induction H.
    - apply refl. apply aeq_abs_same. assumption.
    - apply refltrans_composition with (n_abs x t2).
      + clear H0 IHrefltrans. inversion H; subst.
        * clear H. apply refltrans_lx_b. apply rtrans with (n_abs x t2).
          ** apply step_n_abs. assumption.
          ** apply refl. apply aeq_refl.
        * clear H. apply refltrans_lx_x. apply rtrans with (n_abs x t2).
          ** apply step_n_abs. assumption.
          ** apply refl. apply aeq_refl.
      + assumption.
    - clear H0. apply refltrans_composition with (n_abs x t2).
      + apply refl. apply aeq_abs_same. assumption.
      + assumption. 
Qed. 

Lemma refltrans_n_app_left_lx: forall (t1 t1' t2 : n_sexp), t1 ↠lx t1' -> (n_app t1 t2) ↠lx (n_app t1' t2).
Proof.
  intros t1 t1' t2 H. induction H.
    - apply refl. apply aeq_app; try assumption. apply aeq_refl.
    - apply refltrans_composition with (n_app t0 t2).
      + clear H0 IHrefltrans. inversion H; subst.
        * clear H. apply refltrans_lx_b. apply rtrans with (n_app t0 t2).
          ** apply step_n_app_left. assumption.
          ** apply refltrans_refl.
        * clear H. apply refltrans_lx_x. apply rtrans with (n_app t0 t2).
          ** apply step_n_app_left. assumption.
          ** apply refltrans_refl. 
      + assumption.
    - apply refltrans_composition with (n_app t0 t2).
      + apply refl. apply aeq_app; try assumption. apply aeq_refl.
      + assumption. 
Qed.

Lemma refltrans_n_app_right_lx: forall (t1 t1' t2 : n_sexp), t1' ↠lx t2 -> (n_app t1 t1') ↠lx (n_app t1 t2).
Proof.
  intros t1 t1' t2 H. induction H.
    - apply refl. apply aeq_app; try assumption. apply aeq_refl.
    - apply refltrans_composition with (n_app t1 t2).
      + clear H0 IHrefltrans. inversion H; subst.
        * clear H. apply refltrans_lx_b. apply refltrans_n_app_right. apply rtrans with t2; try apply refltrans_refl. assumption.
        * clear H. apply refltrans_lx_x. apply refltrans_n_app_right. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with (n_app t1 t2).
      + apply refl. apply aeq_app; try assumption. apply aeq_refl.
      + assumption. 
Qed. 
 
Lemma refltrans_n_app_lx: forall (t1 t2 t3 t4 : n_sexp), t1 ↠lx t3 -> t2 ↠lx t4 -> (n_app t1 t2) ↠lx (n_app t3 t4).
Proof.
  intros t1 t2 t3 t4 H1 H2. apply refltrans_composition with (n_app t1 t4).
    - apply refltrans_n_app_right_lx. assumption.
    - apply refltrans_n_app_left_lx. assumption.
Qed.

Lemma refltrans_n_sub_in_lx: forall (t1 t2 t3 : n_sexp) (x : atom), t2 ↠lx t3 -> ([x := t2] t1) ↠lx ([x := t3] t1).
Proof.
  intros t1 t2 t3 x H. induction H.
    - apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
    - apply refltrans_composition with ([x := t2] t1).
      + clear H0 IHrefltrans. inversion H; subst.
        * clear H. apply refltrans_lx_b. apply refltrans_n_sub_in. apply rtrans with t2; try apply refltrans_refl. assumption.
        * clear H. apply refltrans_lx_x. apply refltrans_n_sub_in. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with ([x := t2] t1).
      + apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
      + assumption. 
Qed.

Lemma refltrans_n_sub_out_lx: forall (t1 t2 t3 : n_sexp) (x : atom), t2 ↠lx t3 -> ([x := t1] t2) ↠lx ([x := t1] t3).
Proof.
  intros t1 t2 t3 x H. induction H.
    - apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
    - apply refltrans_composition with ([x := t1] t2).
      + clear H0 IHrefltrans. inversion H; subst.
        * clear H. apply refltrans_lx_b. apply refltrans_n_sub_out. apply rtrans with t2; try apply refltrans_refl. assumption.
        * clear H. apply refltrans_lx_x. apply refltrans_n_sub_out. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with ([x := t1] t2).
      + apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
      + assumption. 
Qed.  
 
Lemma refltrans_n_sub_lx: forall (t1 t2 t3 t4: n_sexp) (x : atom), t1 ↠lx t3 -> t2 ↠lx t4 -> ([x := t1] t2) ↠lx ([x := t3] t4).
Proof.
  intros t1 t2 t3 t4 x H1 H2. apply refltrans_composition with ([x := t1] t4).
    - apply refltrans_n_sub_out_lx. assumption.
    - apply refltrans_n_sub_in_lx. assumption.
Qed.

Lemma refltrans_m_subst_lx: forall t1 t2 t3 x, t1 ↠lx t2 -> ({x := t1}t3) ↠lx ({x := t2}t3).
Proof.
  intros t1 t2 t3 x H. induction H.
    - apply refl. apply aeq_m_subst_in. assumption.
    - apply refltrans_composition with ({x := t2} t3).
      + inversion H; subst.
        * apply refltrans_lx_b. apply refltrans_m_subst1. apply rtrans with t2; try apply refltrans_refl. assumption.
        * apply refltrans_lx_x. apply refltrans_m_subst1. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with ({x := t2} t3).
      + apply refl. apply aeq_m_subst_in. assumption.
      + assumption.
Qed.
(* end hide *)
(**
The proof strategy is similar to  %\cite{nakazawaCompositionalConfluenceProofs2016}%, where the authors prove that the $\lambda_x$-calculus satisfies the compositional Z property, which is an extension of the Z property %\cite{oostromDraftYourMind2007,dehornoy2008z}%, a promising technique used to prove confluence of reduction systems %\cite{vanoostrom:LIPIcs.FSCD.2021.24,felgenhauerProperty2016}%. In a nutshell, a function [f] has the Z property for a binary relation [R] if the following diagram holds:

  $\centerline{\xymatrix{ t_1 \ar[r]_R & t_2 \ar@{.>>}[dl]^R\\ f t_1 \ar@{.>>}[r]_R & f t_2}}$

For the $\lambda_x$-calculus, we take $R$ as the reduction relation $\to_{lx}$, and [f] as the composition of two functions, the complete permutation [P] and the complete development [B], recursively defined as:
*)

Fixpoint P (t : n_sexp) :=
  match t with
  | n_var x => n_var x
  | n_abs x t1 => n_abs x (P t1)
  | n_app t1 t2 => n_app (P t1) (P t2)
  | n_sub t1 x t2 => {x := (P t2)}(P t1)
  end.

Fixpoint B (t : n_sexp) :=
  match t with
  | n_var x => n_var x
  | n_abs x t1 => n_abs x (B t1)
  | n_app t1 t2 =>
      match t1 with
      | n_abs x t3 => {x := (B t2)}(B t3)
      | _ => n_app (B t1) (B t2)
      end
  | n_sub t1 x t2 => n_sub (B t1) x (B t2)
  end.

(** The complete permutation function [P] and the complete development [B] have several interesting properties. In what follows, we will list the most relevant ones to show how to get the confluence proof for the $\lambda_x$-calculus. The first point to be noticed is that [P t] removes all explicit substitution of [t], therefore [P t] is a pure term, that is proved by induction on [t]:
 *)

Lemma pure_P: forall t, pure (P t).
Proof.
  induction t.
  - simpl. apply pure_var.
  - simpl. apply pure_abs. assumption.
  - simpl. apply pure_app; assumption.
  - simpl. apply pure_m_subst; assumption.
Qed.

(** The [B] function does not introduce explicit substitutions to a pure term:
 *)
Lemma pure_B: forall t, pure t -> pure (B t).
Proof.
  intros t H. induction H as [ x | t1 t2 | x t1].
  - simpl. apply pure_var.
  - simpl. destruct t1.
    + simpl in *. apply pure_app;assumption.
    + apply pure_m_subst.
       * simpl in IHpure1. inversion IHpure1. assumption.
       * assumption.
    + apply pure_app;assumption.
    + simpl in IHpure1. inversion IHpure1.
  - simpl. apply pure_abs. assumption.
Qed.

(* begin hide *)
Lemma notin_P: forall t x, x `notin` fv_nom t -> x `notin` fv_nom (P t).
Proof.
  induction t as [ y | y t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 y t2 IHt2].
  - intros x Hnotin. simpl in *. assumption.
  - intros x Hnotin. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHt1. assumption. 
  - intros x Hnotin. simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply IHt1; assumption.
    + apply notin_union_2 in Hnotin. apply IHt2; assumption.
  - intros x Hnotin. simpl in *. pose proof Hnotin as Hnotin'. apply notin_union_1 in Hnotin. apply notin_union_2 in Hnotin'. unfold m_subst. pose proof in_or_notin as Hor. specialize (Hor x (fv_nom (P t1))). destruct Hor.
    + apply fv_nom_remove.
      * apply IHt2; assumption.
      * apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin]. 
        ** subst. apply notin_remove_3; reflexivity.
        ** apply notin_remove_2. apply IHt1. assumption. 
    + apply fv_nom_remove.
      * apply IHt2; assumption.
      * apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
        ** subst. apply notin_remove_3; reflexivity.
        ** apply notin_remove_2. apply IHt1. assumption.
Qed.

Lemma fv_nom_B_n_app: forall t1 t2 x, x `notin` fv_nom (B t1) -> x `notin` fv_nom (B t2) -> x `notin` fv_nom (B (n_app t1 t2)).
Proof.
  induction t1 as [ y | y t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros t2 x Hnotin Hnotin'. simpl in *. apply notin_union.
    + assumption.
    + assumption.
  - intros t2 x Hnotin Hnotin'. simpl in Hnotin. simpl B. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. apply fv_nom_remove_eq. assumption.
    + apply fv_nom_remove.
        * assumption.
        * apply notin_remove_2. assumption.
  - intros t' x Hnotin Hnotin'. change (B (n_app (n_app t1 t2) t')) with (n_app (B (n_app t1 t2)) (B t')). change (fv_nom (n_app (B (n_app t1 t2)) (B t'))) with (fv_nom (B (n_app t1 t2)) `union` fv_nom (B t')). apply notin_union; assumption.
  - intros t' x Hnotin Hnotin'. simpl. apply notin_union.
    + apply notin_union.
      * simpl in Hnotin. apply notin_union_1 in Hnotin. assumption.
      * simpl in Hnotin. apply notin_union_2 in Hnotin. assumption.
    + assumption.
Qed.

Lemma notin_B: forall t x, x `notin` (fv_nom t) -> x `notin` (fv_nom (B t)).
Proof.
  induction t as [ z | z t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros x Hnotin. simpl in *. assumption.
  - intros x Hnotin. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + apply notin_remove_3. assumption.
    + apply notin_remove_2. apply IHt1. assumption.
  - intros x Hnotin. simpl in Hnotin. apply fv_nom_B_n_app.
    + apply IHt1. apply notin_union_1 in Hnotin. assumption.
    + apply IHt2. apply notin_union_2 in Hnotin. assumption.
  - intros x Hnotin. simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
      * apply notin_remove_3. assumption.
      * apply notin_remove_2. apply IHt1. assumption.
    + apply IHt2. apply notin_union_2 in Hnotin. assumption.
Qed.    

(* end hide *)
(** The Z property for the $\lambda_x$-calculus is proved via an extension called the _Compositional Z_ property, as presented in %\cite{nakazawaCompositionalConfluenceProofs2016}%. It is called compositional because, under certain conditions, if the reduction relation $R$ to be proved confluent can be decomposed into two subrelations, then it suffices to prove a Z-like property for each of them separately. In particular, for the $\lambda_x$-calculus we have $\to_{lx} = \to_b \cup \to_x$, and the proof of the compositional Z property is given by the following diagram:
%\begin{equation}\label{lx:zprop-proof}
 \xymatrix{ t_1 \ar@[blue][r]_{x} & t_2 \ar@[blue]@{.>>}[dl]^{x} & & & t_1 \ar[r]_{b} & t_2 \ar@{.>>}[dl]^{lx}\\
P\ t_1 \ar@[green]@{.>>}[r]_{x} \ar@[red]@{.>>}[d]_{lx} & P\ t_2 & & & B(P\ t_1) \ar@{.>>}[r]_{lx} & B(P\ t_2) \\
 B(P\ t_1) \ar@[orange]@{.>>}[r]_{lx} & B(P\ t_2) & & & & \\}
\end{equation}%

The proof that the complete permutation function [P] is a Z function for the relation $\to_x$ (blue and green arrows) uses the fact that the explicit substitution implements the metasubstitution when the term being substituted is pure, i.e., when it does not have an explicit substitution operator. This is formalized in the next lemma. Note that the hypothesis that [t1] is pure is needed because the $\lambda_x$-calculus does not have composition of explicit substitutions (cf. %\cite{kesnerTheoryExplicitSubstitutions2009a}%), and hence the propagation of the outermost substitution $[y := t_2]$ in the term $[y := t_2]([x := t_1]t)$ must be delayed until the inner substitution $[x := t_1]$ is completely propagated.
 *)

Lemma pure_scx: forall t1 x t2, pure t1 -> ([x := t2]t1) ↠x ({x := t2}t1).
Proof.
  induction t1 as [y | t1' y IH | t1' t2' IH1 IH2 | t1' t2' y IH2 IH1 ] using n_sexp_size_induction. 
  - intros x t2 Hpure. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + subst. apply rtrans with t2.
      * apply step_redex. apply scx_aeq_step with ([y := t2] n_var y) t2.
        ** apply aeq_refl.
        ** apply step_var.
        ** apply aeq_refl.
      * apply refltrans_refl.
    + apply rtrans with (n_var y).
      * apply step_redex. apply scx_aeq_step with  ([x := t2] n_var y) (n_var y).
        ** apply aeq_refl.
        ** apply step_gc. symmetry; assumption.
        ** apply aeq_refl.        
      * apply refltrans_refl.
  - intros x t2 Hpure. case (x == y).
    + intro Heq. subst. apply rtrans with (n_abs y t1').
      * apply step_redex. apply scx_aeq_step with ([y := t2] n_abs y t1') (n_abs y t1').
        ** apply aeq_refl.
        ** apply step_abs1.
        ** apply aeq_refl.
      * unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply refltrans_refl.
    + intro Hneq. pose proof in_or_notin as Hin. specialize (Hin y (fv_nom t2)). destruct Hin as [Hin | Hnotin].
      * pick fresh z for ({{x}} \u {{y}} \u fv_nom t1' \u fv_nom t2). apply rtrans with (n_abs z ([x := t2] (swap y z t1'))).
        ** apply step_redex. apply scx_aeq_step with ([x := t2] n_abs y t1') (n_abs z ([x := t2] swap y z t1')).
           *** apply aeq_refl.
           *** apply step_abs3.
               **** symmetry; assumption.
               **** apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. symmetry; assumption.
               **** apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. symmetry; assumption.
               **** assumption.
               **** do 2 apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               **** repeat apply notin_union_2 in Fr. assumption.
           *** apply aeq_refl.
        ** apply refltrans_composition with (n_abs z ({x := t2} swap y z t1')).
           *** apply refltrans_n_abs. apply IH.
               **** simpl. rewrite swap_size_eq. lia.
               **** apply pure_swap. inversion Hpure; subst. assumption.
           *** apply refl. apply aeq_sym. apply aeq_m_subst_abs_neq.
               **** assumption.
               **** apply notin_union.
                    ***** repeat apply notin_union_2 in Fr. assumption.
                    ***** apply notin_union.
                    ****** simpl. apply notin_remove_2. do 2 apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ****** apply notin_union_1 in Fr. assumption.
      * apply rtrans with (n_abs y ([x := t2] t1')).
        ** apply step_redex. apply scx_aeq_step with ([x := t2] n_abs y t1') (n_abs y ([x := t2] t1')).
           *** apply aeq_refl.
           *** apply step_abs2.
               **** symmetry; assumption.
               **** assumption.
           *** apply aeq_refl.
        ** apply refltrans_composition with (n_abs y ({x := t2} t1')).
           *** apply refltrans_n_abs. apply IH.
               **** simpl. lia.
               **** inversion Hpure; subst. assumption.
           *** apply refl. pick fresh z for (fv_nom t2 \u fv_nom t1' \u {{x}} \u {{y}}). apply aeq_trans with (n_abs z ({x := t2} (swap y z t1'))).
               **** apply aeq_abs_diff.
                    ***** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
                    ***** apply fv_nom_remove.
                    ****** assumption.
                    ****** apply notin_remove_2. apply notin_fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ***** apply aeq_trans with ({vswap z y x := swap z y t2} swap z y (swap y z t1')).
                  ******** rewrite (swap_symmetric _ y z). rewrite swap_involutive. rewrite vswap_not.
                  ********* apply aeq_m_subst_in. apply aeq_sym. apply aeq_swap_reduction.
                  ********** apply notin_union_1 in Fr. assumption.
                  ********** assumption.
                  ********* do 2 apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. symmetry; assumption.
                  ********* symmetry; assumption.
                  ******** apply aeq_sym. apply aeq_swap_m_subst.
               **** apply aeq_sym. unfold m_subst at 1. rewrite subst_rec_fun_equation. destruct (x == y).
                    ***** contradiction.
                    ***** destruct (atom_fresh
                                      (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs y t1')) (singleton x)))) as [z']. assert (Hnotin' := n0). apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. case (y == z'). 
                    ****** intro Heq. subst. rewrite swap_id. case (z == z').
                    ******* intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ******* intro Hneq'. apply aeq_abs_diff.
                    ******** symmetry; assumption.
                    ******** apply fv_nom_remove.
                    ********* apply notin_union_1 in Hnotin'. assumption.
                    ********* apply notin_remove_2. apply notin_fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ******** apply aeq_trans with ({ vswap z z' x := swap z z' t2} swap z z' (swap z' z t1')).
                    ********* rewrite vswap_not.
                    ********** rewrite (swap_symmetric _ z' z). rewrite swap_involutive. apply aeq_m_subst_in. apply aeq_sym. apply aeq_swap_reduction.
                    *********** apply notin_union_1 in Fr; assumption.
                    *********** apply notin_union_1 in Hnotin'; assumption.
                    ********** do 2 apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. symmetry; assumption.
                    ********** repeat apply notin_union_2 in Hnotin'. apply notin_singleton_1 in Hnotin'. symmetry; assumption.
                    ********* apply aeq_sym. apply aeq_swap_m_subst.
                    ****** intro Hneq'. destruct n0. 
                    ******* contradiction. 
                    ******* case (z == z'). 
                    ******** intro Heq. subst. apply aeq_refl. 
                    ******** intro Hneq''. apply aeq_abs_diff. 
                    ********* symmetry; assumption. 
                    ********* apply fv_nom_remove.
                    ********** apply notin_union_1 in Hnotin'. assumption.
                    ********** apply notin_remove_2. apply notin_fv_nom_swap_neq.
                    *********** symmetry; assumption.
                    *********** symmetry; assumption.
                    *********** assumption.
                    ********* apply aeq_trans with ({ vswap z z' x := swap z z' t2} swap z z' (swap y z t1')).
                    ********** rewrite vswap_not.
                    *********** apply aeq_trans with ({x := t2} swap z z' (swap y z t1')).
                    ************ apply aeq_m_subst_out. apply aeq_sym. rewrite (swap_symmetric _ z z'). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y z'). apply aeq_swap_swap.
                    ************* apply notin_union_2 in Hnotin'. apply notin_union_1 in Hnotin'. simpl in Hnotin'.  apply notin_remove_1 in Hnotin'. destruct Hnotin'; assumption.
                    ************* apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ************ apply aeq_m_subst_in. apply aeq_sym. apply aeq_swap_reduction.
                    ************* apply notin_union_1 in Fr; assumption.
                    ************* apply notin_union_1 in Hnotin'; assumption.
                    *********** do 2 apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. symmetry; assumption.
                    *********** repeat apply notin_union_2 in Hnotin'. apply notin_singleton_1 in Hnotin'. symmetry; assumption.
                    ********** apply aeq_sym. apply aeq_swap_m_subst.                      
  (** %\noindent {\bf Proof.}% The proof is by induction on the size of the term [t1], and the interesting case is the abstraction case, i.e., when $t_1 = \lambda_y.t_1'$ and we need to prove that $[x := t_2](\lambda_y.t_1') \tto_x \metasub{(\lambda_y.t_1')}{x}{t_2}$. There are two cases:
%\begin{enumerate}
 \item $(x = y)$: $[y := t_2](\lambda_y.t_1') \longrightarrow_{abs1} \lambda_y.t_1' = \metasub{(\lambda_y.t_1')}{y}{t_2}$.
 \item $(x \neq y)$: Consider the following subcases:
  \begin{enumerate}
   \item if $y\in fv(t_2)$ then let $z$ be a fresh variable: $[x := t_2](\lambda_y.t_1') \longrightarrow_{abs3} \lambda_z. [x := t_2](\swap{y}{z}{t_1'}) \tto_x^{(i.h.)} \lambda_z.\metasub{(\swap{y}{z}{t_1'})}{x}{t_2} \stackrel{(\star)}{=_\alpha}  \metasub{(\lambda_y.t_1')}{x}{t_2}$.
   \item if $y\notin fv(t_2)$ then $[x := t_2](\lambda_y.t_1') \longrightarrow_{abs2} \lambda_y.([x := t_2] t_1') \tto_x^{(i.h.)} \lambda_y.(\metasub{t_1'}{x}{t_2}) \stackrel{(\star)}{=_\alpha}  \metasub{(\lambda_y.t_1')}{x}{t_2}$. 
  \end{enumerate}
\noindent where the ($\star$) step (in both subcases) is intuitively simple but has a tricky proof since the definition (\ref{msubst}) of metasubstitution systematically renames variables whenever it crosses an abstraction. \hfill$\Box$
 \end{enumerate}% *)               
  - intros x t2 Hpure. apply rtrans with (n_app ([x := t2]t1') ([x := t2]t2')).
    + apply step_redex. apply scx_aeq_step with ([x := t2] n_app t1' t2') (n_app ([x := t2] t1') ([x := t2] t2')).
      * apply aeq_refl.
      * apply step_app.
      * apply aeq_refl.
    + apply refltrans_composition with (n_app ({x := t2}t1') ({x := t2}t2')).
      * apply refltrans_composition with (n_app ({x := t2} t1') ([x := t2] t2')).
        ** apply refltrans_n_app_left. apply IH1.
           *** simpl. lia.
           *** inversion Hpure; subst. assumption.
        ** apply refltrans_n_app_right. apply IH1.
           *** simpl. lia.
           *** inversion Hpure; subst. assumption.           
      * apply refl. rewrite m_subst_app. apply aeq_refl.
  - intros x t2 Hpure. inversion Hpure.
Qed.

Lemma refltrans_P: forall t, t ↠x (P t).
Proof.
  induction t.
    - simpl. apply refltrans_refl.
    - simpl. apply refltrans_n_abs. assumption.
    - simpl. apply refltrans_n_app; assumption.
    - simpl. apply refltrans_composition with ([x :=  t2] P t1).
      + apply refltrans_n_sub_out. assumption.
      + apply refltrans_composition with ([x := P t2] P t1).
        * apply refltrans_n_sub_in. assumption.
        * apply pure_scx. apply pure_P.
(** %\noindent {\bf Proof.}% The proof is by induction on the term [t]. The interesting case is when [t] is an explicit substitution, i.e., $t = \esub{t_1}{x}{t_2}$. In this case, we have to show that $\esub{t_1}{x}{t_2} \tto_x P(\esub{t_1}{x}{t_2}) =  \metasub{(P\ t_1)}{x}{P\ t_2}$. This is done as follows:

%\begin{mathpar}
 \inferrule{\inferrule{(\star)}{\esub{t_1}{x}{t_2} \tto_x \esub{(P\ t_1)}{x}{P\ t_2}} \and \inferrule{(\star\star)}{\esub{(P\ t_1)}{x}{P\ t_2} \tto_x \metasub{(P\ t_1)}{x}{P\ t_2}}}{\esub{t_1}{x}{t_2} \tto_x \metasub{(P\ t_1)}{x}{P\ t_2}}
\end{mathpar}%

%\noindent% where $(\star)$ is proved by the induction hypothesis and $(\star\star)$, by Lemma [pure_scx], since $P\ t_1$ is pure by Lemma [pure_P]. $\hfill\Box$ *)
Qed.

(** Therefore, Lemma [refltrans_P] proves the blue arrows in %(\ref{lx:zprop-proof})%. The proof that $P\ t_1 \tto_x P\ t_2$ (green arrow in %(\ref{lx:zprop-proof})%) is obtained by Lemma [scx_P] below. Note that the complete permutation $P$ replaces every explicit substitution in the input term $t$ with the corresponding metasubstitution in the output $P\ t$. Some auxiliary results are needed for [scx_P]. The important ones are: *)

Lemma aeq_swap_P: forall t x y, (P (swap x y t)) =α (swap x y (P t)).
Proof.
  induction t as [ z | z t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros x y. simpl. apply aeq_refl.
  - intros x y. simpl. apply aeq_abs_same. apply IHt1.
  - intros x y. simpl. apply aeq_app.
    + apply IHt1.
    + apply IHt2.
  - intros x y. simpl. apply aeq_trans with  ({vswap x y z := (swap x y (P t2))} (swap x y (P t1))).
    + apply aeq_m_subst_eq.
      * apply IHt1.
      * apply IHt2.
    + apply aeq_sym. apply aeq_swap_m_subst.
Qed.

(* begin hide *)
Lemma aeq_swap_B: forall t x y, (swap x y (B t)) =α (B (swap x y t)).
Proof.
  induction t as [ z | z t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros x y. simpl. apply aeq_refl.
  - intros x y. simpl. apply aeq_abs_same. apply IHt1.
  - intros x y. generalize dependent t1. intro t1. case t1.
    + intros x' IH. simpl in *. apply aeq_app. 
       * apply aeq_refl. 
       * apply IHt2. 
    + intros x' t IH. simpl B. apply aeq_trans with ({vswap x y x' := (swap x y (B t2))} (swap x y (B t))).
      * apply aeq_swap_m_subst.
      * apply aeq_m_subst_eq.
        ** simpl in IH. specialize (IH x y). inversion IH; subst.
           *** assumption.
           *** contradiction.
        ** apply IHt2.
    + intros t' t'' IH. change (swap x y (B (n_app (n_app t' t'') t2))) with (n_app (swap x y ((B(n_app t' t'')))) (swap x y ((B t2)))). change (B (swap x y (n_app (n_app t' t'') t2))) with (n_app (B (n_app (swap x y t') (swap x y t''))) (B (swap x y t2))). apply aeq_app.
      * apply IH.
      * apply IHt2.
    + intros t' x' t'' IH. change (swap x y (B (n_app ([x' := t''] t') t2))) with (n_app (swap x y (B ([x' := t''] t'))) (swap x y (B t2))). change (B (swap x y (n_app ([x' := t''] t') t2))) with (n_app (B (swap x y (([x' := t''] t')))) (B (swap x y (t2)))). apply aeq_app.
      * apply IH.
      * apply IHt2.
  - intros x y. simpl. apply aeq_sub_same.
    + apply IHt1.
    + apply IHt2.
Qed.
(* end hide *)

Lemma aeq_P: forall t1 t2, t1 =α t2 -> (P t1) =α (P t2).
Proof.
  induction 1.
  - apply aeq_refl.
  - simpl. apply aeq_abs_same. apply IHaeq.
  - simpl. apply aeq_abs_diff.
    + assumption.
    + apply notin_P. assumption.
    + apply aeq_trans with (P (swap y x t2)).
      * assumption.
      * apply aeq_swap_P.
  - simpl. apply aeq_app; assumption.
  - simpl. apply aeq_m_subst_eq; assumption.
  - simpl. apply aeq_m_subst_neq.
    + assumption.
    + assumption.
    + apply notin_P. assumption.
    + apply aeq_trans with (P (swap y x t1')).
      * assumption.
      * rewrite (swap_symmetric _ y x). apply aeq_swap_P.
Qed.

(** Lemma [aeq_swap_P] is proved by induction on the term [t], while [aeq_P] is by induction on the $\alpha$-equivalence relation. We are now ready to prove Lemma [scx_P] using induction on the reduction $t_1 \to_x t_2$: 
 *)

Lemma scx_P: forall t1 t2, (t1 →x t2) -> (P t1) =α (P t2).
Proof.
  intros t1 t2 H. induction H.
  - induction H. inversion H0; subst.
    + apply aeq_P in H. simpl in H. rewrite m_subst_var_eq in H. apply aeq_P in H1. apply aeq_trans with (P u'); assumption.
    + apply aeq_P in H. simpl in H. rewrite m_subst_var_neq in H.
      * apply aeq_P in H1. apply aeq_trans with (n_var x); assumption.
      * assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. rewrite m_subst_abs_eq in H. apply aeq_trans with (n_abs y (P t1)); assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. apply aeq_trans with ({y := P t2} n_abs x (P t1)).
        ** assumption.
        ** apply aeq_trans with (n_abs x ({y := P t2} P t1)).
           *** apply aeq_m_subst_n_abs_neq_notin.
               **** assumption.
               **** apply notin_P. assumption.
           *** assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. apply aeq_trans with ({y := P t2} n_abs x (P t1)).
        ** assumption.
        ** apply aeq_trans with (n_abs z ({y := P t2} P (swap x z t1))).
           *** apply aeq_trans with (n_abs z ({y := P t2} (swap x z (P t1)))).
               **** apply aeq_m_subst_abs_neq.
                    ***** symmetry; assumption.
                    ***** apply notin_union.
                    ****** apply notin_P; assumption.
                    ****** apply notin_union.
                    ******* simpl. apply notin_remove_2. apply notin_P; assumption.
                    ******* apply notin_singleton. symmetry; assumption.
               **** apply aeq_abs_same. apply aeq_m_subst_out. apply aeq_sym. apply aeq_swap_P. 
           *** assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. rewrite m_subst_app in H. apply aeq_trans with (n_app ({y := P t3} P t1) ({y := P t3} P t2)); assumption.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply aeq_app.
    + assumption.
    + apply aeq_refl.
  - simpl. apply aeq_app.
    + apply aeq_refl.
    + assumption.
  - simpl. apply aeq_m_subst_eq.
    + assumption.
    + apply aeq_refl.
  - simpl. apply aeq_m_subst_eq.
    + apply aeq_refl.
    + assumption.
(** %\noindent {\bf Proof.}% The proof is by induction on the reduction $t_1 \to_x t_2$. The non trivial case is when $t_1 \to_{abs3} t_2$. In this case, $t_1 =_{\alpha} \esub{(\lambda_x.t_1')}{y}{t_2'} \to_{abs3} \lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'} =_{\alpha} t_2$, where $x \neq y$ and $z$ is a fresh variable. In this case, the proof is as follows:
%\begin{mathpar}
 \inferrule{\inferrule{t_1 =_{\alpha} \esub{(\lambda_x.t_1')}{y}{t_2'}}{P\ t_1 =_{\alpha} P\ (\esub{(\lambda_x.t_1')}{y}{t_2'})} \and  \inferrule{(\star) \and \inferrule{\lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'} =_{\alpha} t_2}{P\ (\lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'}) =_{\alpha} P\ t_2} }{P\ (\esub{(\lambda_x.t_1')}{y}{t_2'}) =_{\alpha} P\ t_2}}{P\ t_1 =_{\alpha} P\ t_2}
\end{mathpar}%
%\noindent% where $(\star)$ is given by
%\begin{mathpar}
 \inferrule{\inferrule{\inferrule{~}{\metasub{\lambda_x.(P\ t_1')}{y}{P\ t_2'} =_{\alpha}  \lambda_z.\metasub{(\swap{x}{z}{P\ t_1'})}{y}{P\ t_2'}}}{\metasub{\lambda_x.(P\ t_1')}{y}{P\ t_2'} =_{\alpha}  \lambda_z.\metasub{P\ (\swap{x}{z}{t_1'})}{y}{P\ t_2'}}} {P\ (\esub{(\lambda_x.t_1')}{y}{t_2'}) =_{\alpha} P\ (\lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'})}
\end{mathpar}%
 %\hfill%$\Box$
*)
Qed.

(** The red arrow in %(\ref{lx:zprop-proof})% is proved by Lemma [pure_refltrans_B] below, which is proved by induction on the size of the term [t]: *)

Lemma pure_refltrans_B: forall t, pure t ->  t ↠lx (B t).
Proof.
  induction t as [x | t1 x IH | t1 t2 IH1 IH2 | t1 t2 x IH2 IH1 ] using n_sexp_size_induction.
    - intro Hpure. simpl. apply refltrans_refl.
    - intro Hpure. simpl. apply refltrans_n_abs_lx. apply IH.
      + simpl. lia.
      + inversion Hpure; subst. assumption.
    - intro Hpure. inversion Hpure; subst. destruct t1 eqn:Ht1.
      + simpl. apply refltrans_n_app_right_lx. apply IH1.
        * simpl. lia.
        * assumption.
      + apply refltrans_composition with (n_app (B (n_abs x n)) t2).
        * apply refltrans_n_app_left_lx. apply IH1.
          ** simpl. lia.
          ** assumption.
        * simpl. apply refltrans_composition with  ([x := t2](B n)).
          ** apply refltrans_lx_b. apply rtrans with ([x := t2] B n); try apply refltrans_refl. apply step_redex. apply betax_aeq_step with (n_app (n_abs x (B n)) t2) ([x := t2] B n).
             *** apply aeq_refl.
            *** apply step_betax.
            *** apply aeq_refl.
          ** apply refltrans_composition with ([x := B t2] B n).
             *** apply refltrans_n_sub_in_lx. apply IH1.
                **** simpl. lia.
                **** assumption.
             *** apply refltrans_lx_x. apply pure_scx. apply pure_B. inversion H1; subst. assumption.
      + change (B (n_app (n_app n1 n2) t2)) with (n_app (B (n_app n1 n2)) (B t2)). apply refltrans_n_app_lx.
        * apply IH1.
          ** simpl. lia.
          ** assumption.
        * apply IH1.
          ** simpl. lia.
          ** assumption.
      + inversion H1.
    (** %\noindent {\bf Proof.}% The interesting case is when $t$ is an application, i.e., $t = t_1\ t_2$, and we have to show that $t_1\ t_2 \tto_{lx} B(t_1\ t_2)$. If $t_1$ is not an abstraction, then $B(t_1\ t_2) = B(t_1)\ B(t_2)$ and the proof is by induction hypothesis. If $t_1$ is an abstraction, say $t_1 = \lambda_x.t_1'$, then we have to show that $(\lambda_x.t_1')\ t_2 \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)}$, since $B((\lambda_x.t_1')\ t_2) = \metasub{(B\ t_1')}{x}{(B\ t_2)}$:
%\begin{mathpar} \inferrule{\inferrule{\inferrule{\inferrule*[Right={(i.h.)}]{~}{\lambda_x.t_1' \tto_{lx} \lambda_x.B(t_1')}}{\lambda_x.t_1' \tto_{lx} B(\lambda_x.t_1')}}{(\lambda_x.t_1')\ t_2 \tto_{lx} (B(\lambda_x.t_1'))\ t_2} \and \inferrule{(\star)}{(B(\lambda_x.t_1'))\ t_2 \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)}}}{(\lambda_x.t_1')\ t_2 \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)}}
\end{mathpar}%
%\noindent% where $(\star)$ is proved as follows:
%\begin{mathpar}
 \inferrule{ \inferrule{(\lambda_x.B(t_1'))\ t_2 \tto_{b} \esub{(B\ t_1')}{x}{t_2} \and \inferrule{(\star\star)}{\esub{(B\ t_1')}{x}{t_2} \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)} }}{(\lambda_x.B(t_1'))\ t_2 \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)}}}{(B(\lambda_x.t_1'))\ t_2 \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)}}
\end{mathpar}
\noindent% where $(\star\star)$ is proved as follows:
%\begin{mathpar}
\inferrule{\inferrule{\inferrule*[Right={(i.h.)}]{~}{t_2 \tto_{lx} B\ t_2}}{\esub{(B\ t_1')}{x}{t_2} \tto_{lx} \esub{(B\ t_1')}{x}{(B\ t_2)}} \and (\star\star\star) }{\esub{(B\ t_1')}{x}{t_2} \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)}}
\end{mathpar}
\noindent% where the ($\star\star\star$) corresponds to the reduction %\begin{center}$\esub{(B\ t_1')}{x}{(B\ t_2)} \tto_{lx} \metasub{(B\ t_1')}{x}{(B\ t_2)}$\end{center}% that is justified by Lemma [pure_scx] since $(B\ t_1')$ is pure by Lemma [pure_B].
$\hfill\Box$     *)   
    - intro Hpure. inversion Hpure.
Qed.

(** In order to complete the proof of the left diagram in %(\ref{lx:zprop-proof})%, we need to show that $B(P\ t_1) \tto_{lx} B(P\ t_2)$ (orange arrow). From Lemma [scx_P], we have that $P\ t_1 =_{\alpha} P\ t_2$, and we conclude because [B] is stable under $\alpha$-equivalence, as shown by Lemma [aeq_B] below: *)

Lemma aeq_B: forall t1 t2, t1 =α t2 -> (B t1) =α (B t2).
Proof.
  induction t1 as [x | t1' x IH | t1' t2' IH1 IH2 | t1' t2' x IH2 IH1 ] using n_sexp_induction.
  - intros t2 H. inversion H; subst. apply aeq_refl.
  - intros t2 H0. inversion H0; subst.
    + simpl. apply aeq_abs_same. replace t1' with (swap x x t1'). 
      * apply IH.
        ** reflexivity.
        ** rewrite swap_id. assumption.
      * rewrite swap_id. reflexivity.
    + simpl. apply aeq_abs_diff.
       * assumption.
       * apply notin_B. assumption.
       * apply (aeq_trans _ (B (swap y x t0))).
           ** apply aeq_sym. apply IH.
              *** apply aeq_size in H5. rewrite swap_size_eq in H5. symmetry; assumption.
              *** apply aeq_sym; assumption.
           ** apply aeq_sym. apply aeq_swap_B.
  - intros t2 H. inversion H; subst. 
    + generalize dependent t1'. intro t1'. case t1'.
      * intros x IH1 Haeq1 Haeq2. inversion Haeq2; subst. simpl. apply aeq_app.
        ** apply aeq_var.
        ** apply IH2; assumption.
      * intros x t IH1 Haeq1 Haeq2. inversion Haeq2; subst.
        ** simpl. apply aeq_m_subst_eq.
           *** specialize (IH1 (n_abs x t2)). simpl in IH1. apply (aeq_abs_same x) in H2. apply IH1 in H2. inversion H2; subst.
               **** assumption.
               **** rewrite swap_id in H7. assumption.
           *** apply IH2; assumption.
        ** simpl. apply aeq_m_subst_neq.
           *** apply IH2; assumption.
           *** assumption.
           *** simpl. apply notin_B. assumption.
           *** apply IH1 in Haeq2. simpl in Haeq2. inversion Haeq2; subst.
                **** contradiction.
                **** rewrite (swap_symmetric _ x y). assumption.
      * intros t1 t2 IH Haeq1 Haeq2. inversion Haeq2; subst. change (B (n_app (n_app t1 t2) t2')) with (n_app (B (n_app t1 t2)) (B t2')). change (B (n_app (n_app t1'1 t2'1) t2'0)) with (n_app (B (n_app t1'1 t2'1)) (B t2'0)). apply aeq_app.
        ** apply IH. assumption.
        ** apply IH2. assumption.
      * intros t1 x t2 IH Haeq1 Haeq2. inversion Haeq2; subst. 
        ** simpl. apply aeq_app.
           *** simpl in IH. apply IH in Haeq2. simpl in Haeq2. assumption.
           *** apply IH2. assumption.
        ** simpl. apply aeq_app.
           *** apply IH in Haeq2. simpl in Haeq2. assumption.
           *** apply IH2. assumption.
  - intros t2 H. inversion H; subst.
    + simpl. apply aeq_sub_same.
      * replace t1' with (swap x x t1').
        ** apply IH1.
           *** reflexivity.
           *** rewrite swap_id. assumption.
        ** rewrite swap_id. reflexivity.
      * apply IH2; assumption.
    + simpl. apply aeq_sub_diff.
      * apply IH2; assumption.
      * assumption.
      * apply notin_B. assumption.
      * rewrite <- (swap_id t1' x) in H7. apply IH1 in H7.
        ** rewrite swap_id in H7. apply (aeq_trans _ (B (swap y x t1'0))).
           *** assumption.
           *** apply aeq_sym. apply aeq_swap_B.
        ** reflexivity.
Qed.

(** We now proceed to the proof of the second diagram in (%\ref{lx:zprop-proof}%). We have that $t_1 \to_{b} t_2$ and we want to prove that $t_2 \tto_{lx} B(P\ t_1)$ and $B(P\ t_1) \tto_{lx} B(P\ t_1)$. The first part, proved by Lemma [step_b_refltrans_lx_B_P] below, is proved by induction on the reduction $t_1 \to_{b} t_2$ and the tricky step is to prove that $\metasub{t_1}{x}{t_2} \tto_{lx} B(\metasub{t_1}{x}{t_2})$, whose solution is to use the fact that $\to_{lx}$-steps simulate $\to_{\beta}$-steps, that are now defined as in %(\ref{lambda:beta})%, but over [n_sexp] terms. Let us see how it works.
 *)

(* begin hide *)
Inductive beta_redex : Rel n_sexp :=
| step_beta : forall (t1 t2: n_sexp) (x: atom),
    beta_redex (n_app  (n_abs x t1) t2)  ({x := t2}t1).

Inductive beta_aeq: Rel n_sexp :=
| beta_aeq_step: forall t t' u u', t =α t' -> beta_redex t' u' -> u' =α u -> beta_aeq t u.

Definition beta_ctx t u := ctx beta_aeq t u. 
Notation "t →β u" := (beta_ctx t u) (at level 60).
Notation "t ↠β u" := (refltrans beta_ctx t u) (at level 60).
(* end hide *)

(** The simulation of one step $\beta$-reduction of pure terms is proved in the next lemma using induction on the reduction $t_1 \to_{\beta} t_2$: *)

Lemma pure_beta_lx: forall t1 t2, pure t1 -> (t1 →β t2) -> (t1 ↠lx t2).
Proof.
  intros t1 t2 Hpure1 H. induction H.
    - inversion H; subst. inversion H1; subst. apply refltrans_composition with (n_app (n_abs x t0) t3).
      + apply refl. assumption.
      + apply refltrans_composition with ({x := t3} t0).
        * apply rtrans with ([x := t3] t0).
          ** apply b_rule. apply step_redex. apply betax_aeq_step with (n_app (n_abs x t0) t3) ([x := t3] t0); try apply aeq_refl. apply step_betax.
          ** apply refltrans_lx_x. apply pure_scx. assert (Hpure3: pure (n_app (n_abs x t0) t3)).
            *** apply aeq_pure with t1; assumption.
            *** inversion Hpure3.  inversion H5. assumption. 
        * apply refl. assumption.
    - apply refltrans_n_abs_lx. inversion Hpure1. apply IHctx; assumption.
    - apply refltrans_n_app_left_lx. inversion Hpure1. apply IHctx; assumption.
    - apply refltrans_n_app_right_lx. inversion Hpure1. apply IHctx; assumption.
    - inversion Hpure1.
    - inversion Hpure1.
Qed.

(* begin hide *)
Lemma pure_beta_trans: forall t1 t2, pure t1 -> t1 →β t2 -> pure t2.
Proof.
  intros. induction H0.
  - inversion H0; subst. inversion H2; subst. assert (Hpure: pure(n_app(n_abs x t0) t3)).
      + apply aeq_pure with t1; assumption.
      + apply aeq_pure with ({x := t3} t0).
        * assumption.
        * apply pure_m_subst.
          ** inversion Hpure. inversion H6. assumption.
          ** inversion Hpure. assumption.  
  - inversion H. apply pure_abs. apply IHctx. assumption.
  - inversion H. apply pure_app.
    + apply IHctx. assumption.
    + assumption.
  - inversion H. apply pure_app.
    + assumption.
    + apply IHctx. assumption.
  - inversion H.
  - inversion H.
Qed.

Corollary pure_refltrans_beta_lx: forall t1 t2, pure t1 -> (t1 ↠β t2) -> (t1 ↠lx t2).
Proof.
  intros t1 t2 H H1. induction H1.
    - apply refl. assumption.
    - apply refltrans_composition with t2.
      + apply pure_beta_lx; try assumption.
      + apply IHrefltrans. pose proof pure_beta_trans. apply (pure_beta_trans _ t2) in H; assumption.
    - apply refltrans_composition with t2.
      + apply refl. assumption.
      + apply IHrefltrans. apply aeq_pure with t1; assumption.
Qed.

Lemma refltrans_n_app_B_lx: forall t1 t2, pure t1 -> n_app (B t1) (B t2) ↠lx (B (n_app t1 t2)).
Proof.
  induction t1.
  - intros t2 Hpure. simpl. apply refltrans_n_app_right_lx. apply refl. apply aeq_refl.
  - intros t2 Hpure. simpl. apply refltrans_composition with ([x := B t2] B t1).
    + apply rtrans with ([x := B t2] B t1).
      * apply b_rule. apply step_redex. apply betax_aeq_step with (n_app (n_abs x (B t1)) (B t2)) ([x := B t2] B t1).
        ** apply aeq_refl.
        ** apply step_betax.
        ** apply aeq_refl.
      * apply refl. apply aeq_refl.
    + apply refltrans_lx_x. apply pure_scx. apply pure_B. inversion Hpure; subst. assumption.
  - intros t2 Hpure. inversion Hpure; subst; clear Hpure. change (B (n_app (n_app t1_1 t1_2) t2)) with (n_app (B (n_app t1_1 t1_2)) (B t2)). apply refl. apply aeq_refl.
  - intros t2 Hpure. inversion Hpure.
Qed. 

Lemma n_app_refltrans_beta_B: forall t1 t2, (n_app (B t1) (B t2)) ↠β (B (n_app t1 t2)).
Proof.
  induction t1 as [ x | x t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 x t2  IHt2].
  - intro t2. simpl. apply refltrans_n_app_right. apply refl. apply aeq_refl.
  - intro t2. simpl. apply rtrans with ({x := B t2} B t1).
    + apply step_redex. apply beta_aeq_step with (n_app (n_abs x (B t1)) (B t2)) ({x := B t2} B t1).
      * apply aeq_refl.
      * apply step_beta.
      * apply aeq_refl.
    + apply refl. apply aeq_refl.
  - intro t'. change (B (n_app (n_app t1 t2) t')) with (n_app (B (n_app t1 t2)) (B t')). apply refltrans_n_app_left. apply refl. apply aeq_refl.
  - intro t'. simpl. apply refl. apply aeq_refl.
Qed.

Lemma ctx_beta_swap: forall t1 t2 x y, t1 →β t2 -> (swap x y t1) →β (swap x y t2).
Proof.
  intros t1 t2 x y H. induction H.
    - inversion H; subst. inversion H1; subst. apply step_redex. apply beta_aeq_step with (swap x y (n_app (n_abs x0 t0) t3)) ({vswap x y x0 := swap x y t3} swap x y t0).
      + apply aeq_swap. assumption.
      + simpl. apply step_beta.
      + apply aeq_trans with (swap x y ({x0 := t3} t0)).
        * apply aeq_sym. apply aeq_swap_m_subst.        
        * apply aeq_swap. assumption.
    - simpl. apply step_n_abs. apply IHctx.
    - simpl. apply step_n_app_left. apply IHctx.
    - simpl. apply step_n_app_right. apply IHctx.
    - simpl. apply step_n_sub_out. apply IHctx.
    - simpl. apply step_n_sub_in. apply IHctx.
Qed.

Lemma pure_beta_m_subst_compat: forall t1 t2 t3 x, pure t1 -> t1 →β t2 -> ({x := t3} t1) ↠β ({x := t3} t2).
Proof.
  intros t1 t2 t3 x Hpure Hbeta. induction Hbeta using n_sexp_induction_ctx.
  - inversion H; subst. induction H1. apply refltrans_composition with ({x := t3} (n_app (n_abs x0 t0) t4)).
    + apply refl. apply aeq_m_subst_out. assumption.
    + apply refltrans_composition with ({x := t3} ({x0 := t4} t0)).
      * rewrite m_subst_app. destruct (x == x0).
        ** subst. rewrite m_subst_abs_eq. apply rtrans with ({x0 := t3} ({x0 := t4} t0)).
           *** apply step_redex. apply beta_aeq_step with (n_app (n_abs x0 t0) ({x0 := t3} t4)) ({x0 := {x0 := t3} t4} t0).
               **** apply aeq_refl.
               **** apply step_beta.
               **** apply aeq_sym. apply aeq_double_m_subst.
           *** apply refltrans_refl.
        ** apply refltrans_composition with (let (z,_) := (atom_fresh (Metatheory.union (singleton x) (Metatheory.union (singleton x0) 
                                                                                                         (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t0) (fv_nom t4)))))) in 
                                             n_app (n_abs z ({x := t3} swap x0 z t0)) ({x := t3} t4)).
           *** default_simp. apply refltrans_n_app_left. apply refl. apply aeq_m_subst_abs_neq.
               **** assumption.
               **** repeat apply notin_union_3; auto. default_simp.
           *** destruct (atom_fresh (Metatheory.union (singleton x) (Metatheory.union (singleton x0) 
                                                                       (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t0) (fv_nom t4)))))). apply rtrans with ({x := t3} ({x0 := t4} t0)).
               **** apply step_redex. apply beta_aeq_step with (n_app (n_abs x1 ({x := t3} swap x0 x1 t0)) ({x := t3} t4))
                                                               ({x1 := {x := t3} t4} ({x := t3} swap x0 x1 t0)).
                    ***** apply aeq_refl.
                    ***** apply step_beta.
                    ***** pose proof m_subst_lemma as Hsubst. specialize (Hsubst (swap x0 x1 t0) t4 t3 x1 x). apply aeq_trans with ({x := t3} ({x1 := t4} swap x0 x1 t0)).
                    ****** apply aeq_sym. apply m_subst_lemma; auto.
                    ****** apply aeq_m_subst_out. apply aeq_m_subst_neq; auto. apply aeq_refl. rewrite swap_symmetric. apply aeq_refl.
               **** apply refltrans_refl.
      * apply refl. apply aeq_m_subst_out. assumption.
  - case (x0 == x).
    + intro Heq. subst. repeat rewrite m_subst_abs_eq. apply rtrans with (n_abs x t2).
      ** apply step_n_abs. assumption.
      ** apply refl. apply aeq_refl.
    + intro Hneq. apply refltrans_composition with (let (z,_) := (atom_fresh (Metatheory.union (singleton x) (Metatheory.union (singleton x0) 
                                                                                                                (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2) (fv_nom t3)))))) in 
                                                    (n_abs z ({x := t3} swap x0 z t1))).
      * default_simp. apply refl. apply aeq_m_subst_abs_neq.
        ** symmetry; assumption.
        ** apply notin_union.
           *** repeat apply notin_union_2 in n. assumption.
           *** apply notin_union.
               **** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
               **** apply notin_union_1 in n. assumption.
      * default_simp. apply refltrans_composition with (n_abs x1 ({x := t3} swap x0 x1 t2)).
        ** apply refltrans_n_abs. apply H. 
           *** rewrite swap_size_eq. reflexivity.
           *** rewrite swap_size_eq. reflexivity.
           *** apply ctx_beta_swap. assumption.
           *** apply pure_swap. assumption.
        ** apply refl. apply aeq_sym. apply aeq_m_subst_abs_neq.
           **** symmetry; assumption.
           **** apply notin_union.
                ***** repeat apply notin_union_2 in n. assumption.
                ***** apply notin_union.
                ****** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. simpl. apply notin_remove_2. assumption.
                ****** apply notin_union_1 in n. assumption.
  - repeat rewrite m_subst_app. apply refltrans_n_app_left. apply IHHbeta. inversion Hpure. assumption.
  - repeat rewrite m_subst_app. apply refltrans_n_app_right. apply IHHbeta. inversion Hpure. assumption.
  - inversion Hpure.
  - inversion Hpure.
Qed.

Corollary pure_beta_refltrans_m_subst_compat: forall t1 t2 t3 x,  pure t1 -> t1 ↠β t2 -> ({x := t3}t1) ↠β ({x := t3}t2).
Proof.
  intros t1 t2 t3 x Hpure Hbeta. induction Hbeta.
    - apply refl. apply aeq_m_subst_out. assumption.
    - apply refltrans_composition with ({x := t3} t2).
      + apply pure_beta_m_subst_compat; assumption.
      + apply IHHbeta. apply pure_beta_trans with t1; assumption. 
    - apply refltrans_composition with ({x := t3} t2).
      + apply refl. apply aeq_m_subst_out. assumption.
      + apply IHHbeta. apply aeq_pure in H; assumption.
Qed.

Corollary pure_refltrans_beta_m_subst_compat: forall t1 t2 t3 t4 x, pure t3 -> t1 ↠β t2 -> t3 ↠β t4 -> ({x := t1} t3) ↠β ({x := t2} t4).
Proof.
  intros t1 t2 t3 t4 x Hpure Hbeta1 Hbeta2. apply refltrans_composition with ({x := t2} t3).
    - apply refltrans_m_subst1; assumption.
    - apply pure_beta_refltrans_m_subst_compat; assumption.
Qed.

Lemma b_refltrans_beta_P: forall t1 t2, t1 →b t2 -> (P t1) ↠β (P t2).
Proof.
  intros t1 t2 H. induction H.
  - inversion H; subst. inversion H1; subst. apply refltrans_composition with (P(n_app (n_abs x t0) t3)).
    + apply refl. apply aeq_P. assumption.
    + apply rtrans with (P([x := t3] t0)).
      * simpl. apply step_redex. apply beta_aeq_step with (n_app (n_abs x (P t0)) (P t3)) ({x := P t3} P t0).
        ** apply aeq_refl.
        ** apply step_beta.
        ** apply aeq_refl.
      * apply refl. apply aeq_P. assumption.
  - simpl. apply refltrans_n_abs. assumption.
  - simpl. apply refltrans_n_app_left. assumption.
  - simpl. apply refltrans_n_app_right. assumption.
  - simpl. apply pure_beta_refltrans_m_subst_compat.
    + apply pure_P. 
    + assumption.
  - simpl. apply refltrans_m_subst1. assumption.
Qed.    
(* end hide *)

(** One challenging task in this formalization was the proof of the next lemma, which states that substituting the complete developments of its components into the complete development of a term reduces (via $\beta$-reduction) to the complete development of the corresponding metasubstitution. *)

Lemma pure_m_subst_refltrans_beta_B: forall t1 t2 x, pure t1 -> pure t2 ->
                       ({x := B t2} B t1) ↠β (B ({x := t2} t1)).
Proof.
  induction t1 as [y | t1' y IH | t1' t2' IH1 IH2 | t1' t2' y IH2 IH1 ] using n_sexp_size_induction.
  - intros t2 x Hpure1 Hpure2. simpl. case (x == y).
    + intro Heq. subst. repeat rewrite m_subst_var_eq. apply refltrans_refl.
    + intro Hneq. repeat rewrite m_subst_var_neq; try assumption.
      * simpl. apply refltrans_refl.
      * symmetry; assumption.
      * symmetry; assumption.
  - intros t2 x Hpure1 Hpure2. simpl in *. case (x == y).
    + intro Heq. subst. repeat rewrite m_subst_abs_eq. simpl. apply refltrans_refl.
    + intro Hneq. apply refltrans_composition with (let (z,_) := (atom_fresh (Metatheory.union (singleton y) (Metatheory.union (singleton x) (Metatheory.union (fv_nom t2) (fv_nom t1'))))) in (n_abs z ({x := (B t2)} (swap y z (B t1'))))).
      * destruct (atom_fresh (Metatheory.union (singleton y) (Metatheory.union (singleton x) (Metatheory.union (fv_nom t2) (fv_nom t1'))))). apply refl. apply aeq_m_subst_abs_neq.
        ** assumption.
        ** apply notin_union.
           *** apply notin_B. do 2 apply notin_union_2 in n. apply notin_union_1 in n. assumption.
           *** apply notin_union.
               **** simpl. apply notin_remove_2. repeat apply notin_union_2 in n. apply notin_B. assumption.
               **** apply notin_union_2 in n. apply notin_union_1 in n. assumption.
      * destruct (atom_fresh (Metatheory.union (singleton y) (Metatheory.union (singleton x) (Metatheory.union (fv_nom t2) (fv_nom t1'))))). apply refltrans_composition with (n_abs x0 ({x := B t2} B (swap y x0 t1'))).
        ** apply refltrans_n_abs. apply refl. apply aeq_m_subst_out. apply aeq_swap_B.
        ** apply refltrans_composition with (n_abs x0 (B ({x := t2} swap y x0 t1'))).
           *** apply refltrans_n_abs. apply IH.
               **** rewrite swap_size_eq. simpl. lia.
               **** apply pure_swap. inversion Hpure1; subst. assumption.
               **** assumption.
           *** pose proof aeq_m_subst_abs_neq. simpl in *. apply refltrans_composition with (B (n_abs x0 ({x := t2} swap y x0 t1'))).
               **** simpl. apply refltrans_refl.
               **** apply refl. apply aeq_B. apply aeq_sym. apply H. 
                    ***** assumption.
                    ***** auto.
  - intros t2 x Hpure1 Hpure2. rewrite m_subst_app. generalize dependent t1'. intro t1'. case t1'.
    + intros x' IH Hpure. case (x == x').
      * intro Heq. subst. simpl ({x' := B t2} B (n_app (n_var x') t2')). rewrite m_subst_app. repeat rewrite m_subst_var_eq. apply refltrans_composition with (n_app (B t2) (B ({x' := t2} t2'))).
        ** apply refltrans_n_app_right. apply IH.
           *** simpl. lia.
           *** inversion Hpure; subst. assumption.
           *** assumption.
        ** apply n_app_refltrans_beta_B. 
      * intro Hneq. rewrite m_subst_var_neq.
        ** simpl. rewrite m_subst_app. rewrite m_subst_var_neq.
           *** apply refltrans_n_app_right. apply IH.
               **** simpl. lia.
               **** inversion Hpure; subst. assumption.
               **** assumption. 
           *** symmetry; assumption.
        ** symmetry; assumption.
    + intros x' t IH Hpure. inversion Hpure; subst. simpl (B (n_app (n_abs x' t) t2')). case (x == x').
      * intros Heq. subst. apply refltrans_composition with (B (n_app (n_abs x' t) ({x' := t2} t2'))).
        ** simpl. apply refltrans_composition with ({x' := ({x' := (B t2)} (B t2'))} B t).
           *** apply refl. apply aeq_double_m_subst. 
           *** apply refltrans_m_subst1. apply IH.
               **** simpl. lia.
               **** assumption.
               **** assumption.
        ** apply refl. apply aeq_B. apply aeq_app; try apply aeq_refl. rewrite aeq_m_subst_abs. rewrite eq_dec_refl. apply aeq_refl.           
      * intro Hneq. apply refltrans_composition with (let (z, _) := atom_fresh
                                                          (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs x' t)) (singleton x))) in
                                          (B (n_app (n_abs z ({x := t2} swap x' z t)) ({x := t2} t2')))).
        ** destruct (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs x' t)) (singleton x)))) as [z]. simpl. 
           apply refltrans_composition with ({z := ({x := B t2} B t2')} ({x := B t2} swap x' z (B t))).
           *** apply refltrans_composition with ({x := B t2} ({z := B t2'} swap x' z (B t))).
               **** apply pure_beta_refltrans_m_subst_compat.
                    ***** apply pure_m_subst.
                    ****** apply pure_B. inversion H1; subst.  assumption.
                    ****** apply pure_B; assumption.
                    ***** apply refl. apply aeq_sym. destruct (x' == z).
                    ****** subst. rewrite swap_id. apply aeq_refl. 
                    ****** apply aeq_m_subst_neq.
                    ******* apply aeq_refl.
                    ******* symmetry; assumption.
                    ******* apply notin_B. apply notin_union_2 in n. apply notin_union_1 in n. simpl in n. apply notin_remove_1 in n. destruct n.
                    ******** contradiction.
                    ******** assumption.
                    ******* rewrite swap_symmetric. apply aeq_refl.
               **** apply refl. apply m_subst_lemma.
                    ***** repeat apply notin_union_2 in n. apply notin_singleton_1 in n. symmetry; assumption.
                    ***** apply notin_union_1 in n. apply notin_B. assumption.
           *** apply pure_refltrans_beta_m_subst_compat. 
               **** apply pure_m_subst.
                    ***** apply pure_swap. inversion H1; subst. apply pure_B. assumption.
                    ***** apply pure_B. assumption.
               **** apply IH.
                    ***** simpl. lia.
                    ***** assumption.
                    ***** assumption. 
               **** apply refltrans_composition with ({x := B t2} B (swap x' z t)).
                    ***** apply refl. apply aeq_m_subst_out. apply aeq_swap_B.
                    ***** apply IH.
                    ****** simpl. rewrite swap_size_eq. lia.
                    ****** apply pure_swap. inversion H1; subst. assumption.
                    ****** assumption.
        ** destruct (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs x' t)) (singleton x)))) as [z]. apply refl. apply aeq_B. apply aeq_app.
           *** apply aeq_sym. apply aeq_m_subst_abs_neq; assumption.
           *** apply aeq_refl.
    + intros t t' IH Hpure. repeat rewrite m_subst_app. change (B (n_app (n_app t t') t2')) with (n_app (B (n_app t t')) (B t2')). rewrite m_subst_app. change (B (n_app (n_app ({x := t2} t) ({x := t2} t')) ({x := t2} t2'))) with ((n_app (B (n_app ({x := t2} t) ({x := t2} t'))) (B ({x := t2} t2')))). apply refltrans_n_app.
      * specialize (IH (n_app t t')). apply refltrans_composition with (B ({x := t2} n_app t t')).
        ** apply IH.
           *** simpl. lia.
           *** inversion Hpure; subst. assumption.
           *** assumption.
        ** rewrite m_subst_app. apply refltrans_refl. 
      * apply IH.
        ** simpl. lia.
        ** inversion Hpure; subst. assumption.
        ** assumption.
    + intros t x' t' IH Hpure. inversion Hpure; subst. inversion H1.
      (**
%\noindent {\bf Proof}.% The proof is by induction on the size of the term $t_1$. The interesting case is the application case. If $t_1 = t_{11}\ t_{12}$ then we need to prove that %\begin{center}$\metasub{(B (t_{11}\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{(t_{11}\ t_{12})}{x}{t_2})$\end{center}% We proceed by case analysis on the structure of $t_{11}$. If $t_{11}$ is the variable $x$ then our goal is $(B\ t_2)\ (\metasub{(B t_{12})}{x}{B\ t_2} \tto_{\beta} B\ (t_2\ (\metasub{t_{12}}{x}{t_2}))$ and in turn, we proceed by case analysis on the structure of $t_2$. The non-trivial case, again is when $t_2 = \lambda_y.t_2'$:
%{\scriptsize\begin{mathpar}
\inferrule{\inferrule{\inferrule*[Right={(\sf i.h.)}]{~} {\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')} \tto_{\beta} B( \metasub{t_{12}}{x}{\lambda_y.t_2'})}} {\inferrule{\metasub{(B\ t_2')}{y}{(\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')})} \tto_{\beta}  \metasub{(B\ t_2')}{y}{(B(\metasub{t_{12}}{x}{(\lambda_y.t_2')}))}} {(\lambda_y.B\ t_2')\ (\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')}) \tto_{\beta}  \metasub{(B\ t_2')}{y}{(B(\metasub{t_{12}}{x}{(\lambda_y.t_2')}))}}}} {(B\ (\lambda_y.t_2'))\ (\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')} \tto_{\beta} B\ ((\lambda_y.t_2')\ (\metasub{t_{12}}{x}{(\lambda_y.t_2')})))}
\end{mathpar}}%

Another non-trivial case occurs when $t_{11} = \lambda_y.t_{11}'$, leading to the goal  %\begin{center}$\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})$\end{center}%

%\noindent% whose derivation is given by

%\begin{mathpar}
\inferrule{\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}{\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}
\end{mathpar}%

Then we have two cases, either $x = y$ or $x \neq y$:

%\begin{enumerate}
\item $x = y$:
{\small \begin{mathpar}
\inferrule{\inferrule{ \inferrule{ \inferrule{ \inferrule*[Right={(\sf i.h.)}]{~}{\metasub{(B\ t_{12})}{x}{B\ t_2} \tto_{\beta} B \metasub{t_{12}}{x}{t_2}}} {\metasub{(B\ t_{11}')}{y}{(\metasub{(B\ t_{12})}{x}{B\ t_2})} \tto_{\beta} \metasub{(B\ t_{11}')}{y}{B (\metasub{t_{12}}{x}{t_2})}}} {\metasub{(B\ t_{11}')}{y}{(\metasub{(B\ t_{12})}{x}{B\ t_2})} \tto_{\beta} B ((\lambda_y.t_{11}')\ \metasub{t_{12}}{x}{t_2})}} {\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}} {\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}
\end{mathpar}}

\item $x \neq y$:
{\scriptsize\begin{mathpar}
\inferrule{\inferrule{\inferrule{ \inferrule{(\star)} {\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} \metasub{(B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))}{z}{B(\metasub{t_{12}}{x}{t_2})}}}{\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B ((\lambda_z.(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))\ (\metasub{t_{12}}{x}{t_2}))}} {\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}} {\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}
\end{mathpar}}
\end{enumerate}%

%\noindent% where $(\star)$ is obtained by decomposing the reduction

%\noindent {\small $\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} \metasub{(B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))}{z}{B(\metasub{t_{12}}{x}{t_2})}$}%

%\noindent% using %{\small $\metasub{(\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2})}{z}{\metasub{(B\ t_{12})}{x}{B\ t_2}}$}% as the intermediate term, and each subreduction is solved as follows: the first subreduction is an instance of the Substitution Lemma ([m_subst_lemma]) formalized in %\cite{limaFormalizedExtensionSubstitution2023}%, and the second subreduction is obtained by applying the induction hypothesis to the two components of the application:
%{\tiny \begin{mathpar}
\inferrule{\inferrule{~}{\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2} \tto_{\beta} B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2})} \and \inferrule{~}{\metasub{(B\ t_{12})}{x}{B\ t_2} \tto_{\beta} B(\metasub{t_{12}}{x}{t_2})}} {\metasub{(\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2})}{z}{\metasub{(B\ t_{12})}{x}{B\ t_2}} \tto_{\beta} \metasub{(B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))}{z}{B(\metasub{t_{12}}{x}{t_2})}}\end{mathpar}}%
$\hfill\Box$
*)  
  - intros t x Hpure. inversion Hpure.
Qed.

(* begin hide *)
Lemma refltrans_beta_aeq_beta: forall t1 t2 t3, (t1 ↠β t2) -> (t2 =α t3) -> t1 ↠β t3.
Proof.
  intros t1 t2 t3 Hrefl Haeq. apply refltrans_composition with t2.
  - assumption.
  - apply refl. assumption.
Qed.

Lemma beta_n_abs_alpha: forall t t' x, n_abs x t →β t' -> exists y t'', t' = n_abs y t''.
Proof.  
  intros t t' x H. remember (n_abs x t) as t''. induction H.
  - inversion H; subst. apply aeq_n_abs in H0. destruct H0 as [y Habs]. destruct Habs as [t'' Habs]. rewrite Habs in H1. inversion H1.
  - inversion Heqt''; subst. exists x, t2. reflexivity.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
Qed.

Lemma beta_n_abs: forall t t' x, n_abs x t →β t' -> exists t'', t' = n_abs x t''.
Proof.  
  intros t t' x H. remember (n_abs x t) as t''. induction H.
  - inversion H; subst. apply aeq_n_abs in H0. destruct H0 as [y Habs]. destruct Habs as [t'' Habs]. rewrite Habs in H1. inversion H1.
  - inversion Heqt''; subst. exists t2. reflexivity.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
Qed.

Lemma n_abs_step_beta: forall t1 t2 x, n_abs x t1 →β n_abs x t2 -> t1 →β t2.
Proof.
  intros t1 t2 x H. unfold beta_ctx in H. inversion H.
  - clear H1 H2 H. inversion H0. apply aeq_n_abs in H. destruct H as [y H]. destruct H as [t'' H]. rewrite H in H1. inversion H1.
  - assumption.
Qed.

Lemma fv_nom_beta: forall t1 t2 x, x `notin` fv_nom t1 -> t1 →β t2 -> x `notin` fv_nom t2.
Proof.
  intros t1 t2 x Hnotin Hbeta. induction Hbeta.
  - inversion H; subst. inversion H1; subst. apply aeq_fv_nom in H0. simpl in H0. apply aeq_fv_nom in H2. simpl in H2. rewrite H0 in Hnotin. rewrite <- H2. clear H H0 H1 H2. apply fv_nom_remove.
    + apply notin_union_2 in Hnotin. assumption.
    + apply notin_union_1 in Hnotin. assumption.
  - simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHHbeta. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply IHHbeta. assumption.
    + apply notin_union_2 in Hnotin. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. assumption.
    + apply notin_union_2 in Hnotin. apply IHHbeta. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
      * subst. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. apply IHHbeta. assumption.
    + apply notin_union_2 in Hnotin. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. assumption.
    + apply notin_union_2 in Hnotin. apply IHHbeta. assumption.
Qed.

Lemma refltrans_n_abs_step_beta: forall t1 t2 x y, n_abs x t1 ↠β n_abs y t2 -> t1 ↠β (swap x y t2).
Proof.
  intros t1 t2 x y H. remember (n_abs x t1) as t. remember (n_abs y t2) as t'. apply eq_aeq in Heqt. apply eq_aeq in Heqt'. generalize dependent y. generalize dependent x. generalize dependent t2. generalize dependent t1. induction H.
  - intros t3 t4 x H1 y H2. apply refl.
    assert (Haeq: n_abs x t3 =α n_abs y t4).
    {
      apply aeq_trans with t1.
      - apply aeq_sym; assumption.
      - rewrite H2 in H. assumption.
    }
    inversion Haeq; subst.
    + rewrite swap_id. assumption.
    + rewrite (swap_symmetric _ x y). assumption.
  - intros t4 t5 x Haeq1 y Haeq2. apply aeq_sym in Haeq1. assert (Haeq1' := Haeq1).
    apply aeq_n_abs in Haeq1. destruct Haeq1 as [z Haeq1]. destruct Haeq1 as [t6 Haeq1]. subst. assert (Hbeta := H).
    assert (Hrefl: t2 ↠β n_abs y t5).
    {
     apply refltrans_beta_aeq_beta with t3; assumption. 
    }
    apply refltrans_composition with (swap x z t6).
    + apply refl. inversion Haeq1'; subst.
      * rewrite swap_id. assumption.
      * rewrite (swap_symmetric _ x z). assumption.
    + apply beta_n_abs in H. destruct H as [t7 H]. inversion Haeq1'; subst.
      * rewrite swap_id. apply refltrans_composition with t7. apply rtrans with t7.
        ** apply n_abs_step_beta in Hbeta. assumption.
        ** apply refl. apply aeq_refl.
        ** apply IHrefltrans.
           *** apply aeq_refl.
           *** assumption.
      * apply rtrans with (swap x z t7).
        ** apply n_abs_step_beta in Hbeta. apply ctx_beta_swap. assumption.
        ** apply IHrefltrans.
           *** apply aeq_sym. rewrite (swap_symmetric _ x z). apply aeq_abs_swap.
               **** assumption.
               **** apply n_abs_step_beta  in Hbeta. apply fv_nom_beta with t6; assumption.
           *** assumption.              
  - intros t4 t5 x H1 y H2.
    assert (Haeq: n_abs x t4 =α t2).
    {
      apply aeq_trans with t1.
      - apply aeq_sym; assumption.
      - assumption.
    }
    assert (Haeq' := Haeq). apply aeq_n_abs in Haeq. destruct Haeq as [z Haeq]. destruct Haeq as [t6 Haeq]. subst. inversion Haeq'; subst.
    + apply refltrans_composition with t6.
      * apply refl. assumption.
      * apply IHrefltrans.
      ** apply aeq_refl.
      ** assumption.
    + apply refltrans_composition with (swap z x t6).
      * apply refl. assumption.
      * apply IHrefltrans.
        ** apply aeq_abs_diff.
           *** symmetry; assumption.
           *** apply notin_fv_nom_remove_swap_inc. assumption.
           *** rewrite (swap_symmetric _ x z). rewrite swap_involutive. apply aeq_refl.
        ** assumption.
Qed.

Lemma beta_implies_refltrans_B: forall t1 t2, pure t1 -> (t1 →β t2) -> (B t1) ↠β (B t2). 
Proof. 
  intros t1 t2 Hpure Hbeta. induction Hbeta.
  - inversion H; subst. inversion H1; subst. apply refltrans_composition with (B (n_app (n_abs x t0) t3)).
    + apply refl. apply aeq_B. assumption.
    + simpl. apply refltrans_composition with (B ({x := t3} t0)).
      * assert (Hpure2: pure(n_app (n_abs x t0) t3)). 
        ** apply aeq_pure with t1; assumption.
        ** inversion Hpure2. inversion H5. apply pure_m_subst_refltrans_beta_B; assumption.
      * apply refl. apply aeq_B. assumption.
  - simpl. apply refltrans_n_abs. apply IHHbeta. inversion Hpure; subst. assumption.
  - inversion Hbeta; subst.
    + inversion H; subst. inversion H1; subst. apply refltrans_composition with (B (n_app (n_app (n_abs x t0) t3) t2)).
      * apply refl. apply aeq_B. apply aeq_app.
        ** assumption.
        ** apply aeq_refl.
      * apply refltrans_composition with (B (n_app ({x := t3} t0) t2)).
        ** change (B (n_app (n_app (n_abs x t0) t3) t2) ) with (n_app (B (n_app (n_abs x t0) t3)) (B t2)). simpl (B (n_app (n_abs x t0) t3)). apply refltrans_composition with (n_app (B ({x := t3} t0)) (B t2)).
           *** apply refltrans_n_app.
               **** assert (Hpure2: pure(n_app (n_abs x t0) t3)). 
                    ***** inversion Hpure. apply aeq_pure with t1; assumption.
                    ***** inversion Hpure2. inversion H5. apply pure_m_subst_refltrans_beta_B; assumption.
               **** apply refl. apply aeq_refl.
           *** apply n_app_refltrans_beta_B.
        ** apply refl. apply aeq_B. apply aeq_app.
           *** assumption.
           *** apply aeq_refl.
    + inversion Hpure; subst. apply IHHbeta in H2. simpl in *. apply pure_refltrans_beta_m_subst_compat. 
      * apply pure_B. inversion Hpure; subst. inversion H4; subst. assumption.
      * apply refl. apply aeq_refl.
      * clear IHHbeta Hpure H H3. replace (B t3) with (swap x x (B t3)).
        ** apply refltrans_n_abs_step_beta. assumption.
        ** rewrite swap_id. reflexivity.
    + change (B (n_app (n_app t0 t3) t2)) with (n_app (B (n_app t0 t3)) (B t2)). change (B (n_app (n_app t1'0 t3) t2)) with (n_app (B (n_app t1'0 t3)) (B t2)). apply refltrans_n_app.
      * apply IHHbeta. inversion Hpure; subst. assumption.
      * apply refl. apply aeq_refl.
    + change (B (n_app (n_app t0 t3) t2)) with (n_app (B (n_app t0 t3)) (B t2)). change (B (n_app (n_app t0 t2') t2)) with (n_app (B (n_app t0 t2')) (B t2)). apply refltrans_n_app.
      * apply IHHbeta. inversion Hpure; subst. assumption.
      * apply refl. apply aeq_refl.
    + inversion Hpure; subst. inversion H2.
    + inversion Hpure; subst. inversion H2.
  - generalize dependent t2'. generalize dependent t2. case t1.
    + intros x t2 Hpure t2' Hbeta IH. simpl. apply refltrans_n_app.
      * apply refl. apply aeq_refl.
      * apply IH. inversion Hpure; subst. assumption.
    + intros x t t2 Hpure t2' Hbeta IH. simpl. apply refltrans_m_subst1. apply IH. inversion Hpure; subst. assumption.
    + intros t0 t2 t3 Hpure t2' Hbeta IH. change (B (n_app (n_app t0 t2) t3)) with (n_app (B (n_app t0 t2)) (B t3)). change (B (n_app (n_app t0 t2) t2')) with (n_app (B (n_app t0 t2)) (B t2')). apply refltrans_n_app.
      * apply refl. apply aeq_refl.
      * apply IH. inversion Hpure; subst. assumption.
    + intros t0 x t2 t3 Hpure t2' Hbeta IH. inversion Hpure; subst. inversion H1.
  - inversion Hpure.
  - inversion Hpure.
Qed.

Corollary refltrans_beta_B: forall t1 t2, pure t1 -> t1 ↠β t2 -> B t1 ↠β B t2.
Proof.
  intros t1 t2 Hpure Hbeta. induction Hbeta.
  - apply refl. apply aeq_B. assumption.
  - apply refltrans_composition with (B t2).
    + apply beta_implies_refltrans_B; assumption.
    + apply IHHbeta. apply pure_beta_trans with t1; assumption.
  - apply refltrans_composition with (B t2).
    + apply refl. apply aeq_B. assumption.
    + apply IHHbeta. apply aeq_pure in H; assumption.
Qed.
(* end hide *)

(** Now we are ready to prove the first part of the second diagram in %(\ref{lx:zprop-proof})%. As explained before, the challenging case is the one involving the explicit substitution: *)

Lemma step_b_refltrans_lx_B_P: forall t1 t2, t1 →b t2 -> t2 ↠lx (B(P t1)).
Proof. 
  intros t1 t2 H. induction H.
  - inversion H; subst. inversion H1; subst. apply refltrans_composition with ([x := t3] t0).
    + apply refl. apply aeq_sym; assumption.
    + apply refltrans_composition with (B (P (n_app (n_abs x t0) t3))).
      * simpl. apply refltrans_composition with ([x := (B (P t3))] (B (P t0))).
        ** apply refltrans_n_sub_lx.
           *** apply refltrans_composition with (P t3).
               **** apply refltrans_lx_x. apply refltrans_P.
               **** apply pure_refltrans_B. apply pure_P.
           *** apply refltrans_composition with (P t0).
               **** apply refltrans_lx_x. apply refltrans_P.
               **** apply pure_refltrans_B. apply pure_P.
        ** apply refltrans_lx_x. apply pure_scx. apply pure_B. apply pure_P.
      * apply refl. apply aeq_B. apply aeq_P. apply aeq_sym. assumption.
  - simpl. apply refltrans_n_abs_lx. apply IHctx.
  - apply refltrans_composition with (n_app (B (P t1)) (B (P t2))).
    + apply refltrans_n_app_lx.
      * assumption.
      * apply refltrans_composition with (P t2).
        ** apply refltrans_lx_x. apply refltrans_P.
        ** apply pure_refltrans_B. apply pure_P.
    + apply refltrans_n_app_B_lx. apply pure_P.
  - simpl P. apply refltrans_composition with (n_app (B (P t1)) (B (P t2))).
    * apply refltrans_n_app_lx.
      ** apply refltrans_composition with (P t1).
         *** apply refltrans_lx_x. apply refltrans_P.
         *** apply pure_refltrans_B. apply pure_P.
      ** assumption.
    * apply refltrans_n_app_B_lx. apply pure_P.
  - simpl. apply refltrans_composition with (B([x := (P t2)] (P t1))).
    + simpl. apply refltrans_n_sub_lx.
      * apply refltrans_composition with (P t2).
        ** apply refltrans_lx_x. apply refltrans_P.
        ** apply pure_refltrans_B. apply pure_P.
      * apply IHctx. 
    + simpl. apply refltrans_composition with ({x := B (P t2)} B (P t1)).
      * apply refltrans_lx_x. apply pure_scx. apply pure_B. apply pure_P.
      * apply pure_refltrans_beta_lx.
        ** apply pure_m_subst; apply pure_B; apply pure_P.
        ** apply pure_m_subst_refltrans_beta_B; apply pure_P.
  - apply refltrans_composition with (([x := (B (P t2))] (B (P t1)))).
    + apply refltrans_n_sub_lx.
      * assumption.
      * apply refltrans_composition with (P t1).
        ** apply refltrans_lx_x. apply refltrans_P.
        ** apply pure_refltrans_B. apply pure_P.
    + simpl. apply refltrans_composition with ({x := (B (P t2))} (B (P t1))).
      * apply refltrans_lx_x. apply pure_scx. apply pure_B. apply pure_P.
      * apply pure_refltrans_beta_lx.
        ** apply pure_m_subst; apply pure_B; apply pure_P.
        ** apply pure_m_subst_refltrans_beta_B; apply pure_P.
(** %\noindent {\bf Proof.}% Suppose that
%\begin{center}$t_1 = \esub{t_{11}}{x}{t_{12}} \to_{b} \esub{t_{11}'}{x}{t_{12}} = t_2$, with $t_{11} \to_{b} t_{11}'$\end{center}% or
%\begin{center}$t_1 = \esub{t_{11}}{x}{t_{12}} \to_{b} \esub{t_{11}}{x}{t_{12}'} = t_2$, with $t_{12} \to_{b} t_{12}'$.\end{center}%

Both cases have similar proofs, therefore we consider only the first reduction that proceeds as follows:

%{\tiny \begin{mathpar}
\inferrule{ \inferrule{ \inferrule{ \inferrule{~} {t_{11}' \tto_{lx} B (P\ t_{11})} \and \inferrule{(\star)}{t_{12} \tto_{lx} B (P\ t_{12})}} {\esub{t_{11}'}{x}{t_{12}} \tto_{lx} \esub{B (P\ t_{11})}{x}{B( P\ t_{12})}}} {\esub{t_{11}'}{x}{t_{12}} \tto_{lx} B(\esub{(P\ t_{11})}{x}{P\ t_{12}})} \and \inferrule{(\star\star)} {B(\esub{(P\ t_{11})}{x}{P\ t_{12}}) \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})}}
{\inferrule{\esub{t_{11}'}{x}{t_{12}} \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})} {\esub{t_{11}'}{x}{t_{12}} \tto_{lx} B(P(\esub{t_{11}}{x}{t_{12}}))}}
\end{mathpar}}%

%\noindent% where $(\star)$ is easily proved by lemmas [refltrans_P], [pure_P] and [pure_refltrans_B], and $(\star\star)$ is proved as follows:

%\begin{mathpar}
 \inferrule{ \inferrule{ \inferrule{(\star\star\star)}{\esub{(B(P\ t_{11}))}{x}{B(P\ t_{12})} \tto_{lx} \metasub{(B(P\ t_{11}))}{x}{B(P\ t_{12})}} \and (\star\star\star\star) } {\esub{(B((P\ t_{11})))}{x}{B(P\ t_{12})} \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}}) }} {B(\esub{(P\ t_{11})}{x}{P\ t_{12}}) \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})}
\end{mathpar}%

%\noindent% where $(\star\star\star)$ is proved by lemma [pure_pix] since $\to_x \subseteq \to_{lx}$, and $(\star\star\star\star)$ is given by the reduction

%\begin{equation}\label{red:lx}\metasub{(B((P\ t_{11})))}{x}{B(P\ t_{12})}  \tto_{lx}  B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})\end{equation}%

%\noindent% which is the tricky part of the proof. It is proved using the fact that $\to_{lx}$ steps can simulate $\beta$-steps as proved by Lemma [pure_beta_lx]. $\hfill\Box$ *)
Qed.  

(** Finally, the last part of the second diagram in %(\ref{lx:zprop-proof})% is proved by the next lemma: *)

Lemma refltrans_lx_B_P: forall t1 t2, (t1 →b t2) -> (B (P t1)) ↠lx (B (P t2)).
Proof. 
 intros t1 t2 H. apply  pure_refltrans_beta_lx. 
    - apply pure_B. apply pure_P.
    - apply b_refltrans_beta_P in H. apply refltrans_beta_B.
      + apply pure_P.
      + assumption.
(** %\begin{mathpar}
 \inferrule{\inferrule{\inferrule{t_1 \to_b t_2}{P\ t_1 \tto_{\beta} P\ t_2}}{B(P\ t_1) \tto_{\beta} B(P\ t_2)}}{B(P\ t_1) \tto_{lx} B(P\ t_2)}
\end{mathpar}% $\hfill\Box$ *)
Qed.

(** The diagrams in (%\ref{lx:zprop-proof}%) are formalized as the predicate [Z_comp_aeq] used in the next lemma: *)
Lemma lambda_x_Z_comp_aeq: Z_comp_aeq lambdax.
Proof.
  unfold Z_comp_aeq. exists scx_ctx, betax_ctx, P, B. split.
  - intros t1 t2; split.
    + intro Hlx. apply union_or. apply or_comm. inversion Hlx; subst.
      * left. assumption.
      * right. assumption.
    + intro Hunion. inversion Hunion; subst.
      * apply x_rule. assumption.
      * apply b_rule. assumption.
  - split.
    + intros t1 t2 Hx. split.
      * apply scx_P. assumption.
      * unfold comp. apply scx_P in Hx. apply aeq_B. assumption. 
    + split.
      * intros t1 t2 Haeq. unfold comp. apply aeq_B. apply aeq_P. assumption.
      * split.
        ** intro t. apply refltrans_P.
        ** split.
        *** intros t1 t2 H. rewrite H. apply pure_refltrans_B. apply pure_P.
        *** unfold f_is_weak_Z. unfold comp. intros t1 t2 H. split.
            **** apply step_b_refltrans_lx_B_P. assumption.
            **** apply refltrans_lx_B_P. assumption.
Qed.
(** Therefore, we can conclude that the reduction $\to_{lx}$ satisfies the compositional Z-property modulo $\alpha$-equivalence. In %\cite{fmm2021}%, we formalized that the compositional Z property implies the Z property, which in turn implies confluence. These intermediate results are used in the next theorem to conclude that $\to_{lx}$ is confluent. *)
Theorem lambda_x_is_confluent: Confl lambdax.
Proof.
  apply Z_prop_aeq_implies_Confl.
  apply Z_comp_aeq_implies_Z_prop_aeq.
  apply lambda_x_Z_comp_aeq.
Qed.
(**
<<
Proof.
  apply Z_prop_aeq_implies_Confl.
  apply Z_comp_aeq_implies_Z_prop_aeq.
  apply lambda_x_Z_comp_aeq.
Qed.
>>
 *)

