(* begin hide *)
Require Import Arith Lia.

Require Import Metalib.Metatheory.
Require Import Metalib.LibDefaultSimp.
Require Import Metalib.LibLNgen. 
Require Import PeanoNat.

Lemma in_or_notin: forall x s, x `in` s \/ x `notin` s.
Proof.
  intros. pose proof notin_diff_1. specialize (H x s s).
  rewrite AtomSetProperties.diff_subset_equal in H.
  - apply or_comm. apply H. apply notin_empty_1.
  - reflexivity.
Qed.

Lemma diff_remove_2: forall x y s, x <> y -> x `notin` remove y s -> x `notin` s.
Proof.
  intros. default_simp.
Qed. 

Lemma remove_singleton_empty: forall x, remove x (singleton x) [=] empty.
Proof.
  intros. rewrite AtomSetProperties.singleton_equal_add. rewrite AtomSetProperties.remove_add.
  - reflexivity.
  - apply notin_empty_1.
Qed.
  
Lemma remove_singleton: forall t1 t2, remove t1 (singleton t1) [=] remove t2 (singleton t2).
Proof.
  intros t1 t2. repeat rewrite remove_singleton_empty. reflexivity.
Qed.

Lemma notin_singleton_is_false: forall x, x `notin` (singleton x) -> False.
Proof.
  intros. intros. apply notin_singleton_1 in H. contradiction.
Qed.

Lemma double_remove: forall x s, remove x (remove x s) [=] remove x s.
Proof.
  intros. pose proof AtomSetProperties.remove_equal.
  assert (x `notin` remove x s). apply AtomSetImpl.remove_1. reflexivity.
  specialize (H (remove x s) x). apply H in H0. assumption.
Qed.

Lemma remove_symmetric: forall x y s, remove x (remove y s) [=] remove y (remove x s).
Proof.
  intros. split.
  - intros. case (a == x); intros; case (a == y); intros; subst. apply AtomSetImpl.remove_3 in H.
    + rewrite double_remove. assumption.
    + apply remove_iff in H. inversion H. contradiction.
    + apply remove_iff in H. inversion H. apply remove_iff in H0. inversion H0. contradiction.
    + pose proof H. apply AtomSetImpl.remove_3 in H. apply AtomSetImpl.remove_2.
      * symmetry; assumption.
      * apply AtomSetImpl.remove_2.
        ** symmetry; assumption.
        ** apply AtomSetImpl.remove_3 in H. assumption.
  - intros. case (a == x); intros; case (a == y); intros; subst.
    + apply AtomSetImpl.remove_3 in H. rewrite double_remove. assumption.
    + apply remove_iff in H. inversion H. apply remove_iff in H0. inversion H0. contradiction.
    + apply remove_iff in H. inversion H. contradiction.
    + pose proof H. apply AtomSetImpl.remove_3 in H. apply AtomSetImpl.remove_2.
      * symmetry; assumption.
      * apply AtomSetImpl.remove_2.
        ** symmetry; assumption.
        ** apply AtomSetImpl.remove_3 in H. assumption.
Qed.

Lemma remove_empty: forall x, remove x empty [=] empty.
Proof.
  intros. pose proof notin_empty. specialize (H x). apply AtomSetProperties.remove_equal in H. assumption.
Qed.

Lemma diff_remove: forall x y s, x <> y -> x `notin` s -> x `notin` remove y s.
Proof.
  intros. apply notin_remove_2. assumption.
Qed.
(* end hide *)

(** * Introduction *)

(** We present a framework for studying properties of extensions of the $\lambda$-calculus%\cite{barendregtLambdaCalculusIts1984a}%, which is based on a nominal approach %\cite{gabbayNewApproachAbstract2002}%. In the nominal setting, variables are represented by atoms, structureless entities with a decidable equality:

<<
Parameter eq_dec : forall x y : atom, {x = y} + {x <> y}.
>>

%\noindent% therefore different names mean different atoms and different variables. The nominal approach is close to the usual paper and pencil notation used in $\lambda$-calculus, whose grammar of terms is given by:

%\begin{equation}\label{lambda:grammar}
 t ::= x \mid \lambda_x.t \mid t\ t
\end{equation}%

%\noindent% where $x$ represents a variable taken from an enumerable set, $\lambda_x.t$ is an abstraction, and $t\ t$ is an application. The abstraction is the only binding operator: in the expression $\lambda_x.t$, $x$ binds in $t$, called the scope of the abstraction. This means that every free occurrence of $x$ in $t$ becomes bound in $\lambda_x.t$. A variable that is not in the scope of an abstraction is free. A variable in a term is either bound or free, but note that a variable can occur both bound and free in the same term, as in $(\lambda_y. y)\ y$. The main rule of the $\lambda$-calculus, named $\beta$-reduction, is given by:

%\begin{equation}\label{lambda:beta}
 (\lambda_x.t)\ u \to_{\beta} \metasub{t}{x}{u}
\end{equation}%
%\noindent% where $\metasub{t}{x}{u}$ represents the result of substituting all free occurrences of variable $x$ in $t$ with $u$, renaming bound variables whenever needed to avoid capturing free variables of $u$. We call $t$ the body of the metasubstitution, and $u$ its argument. In other words, $\metasub{t}{x}{u}$ is a metanotation for a capture-free substitution. For instance, the $\lambda$-term $(\lambda_x\lambda_y.x\ y)\ y$ has both bound and free occurrences of the variable $y$, and in order to $\beta$-reduce it, one has to substitute the free variable $y$ for all free occurrences of the variable $x$ in the term $(\lambda_y.x\ y)$. A straight substitution would capture the free variable $y$, %{\it i.e.}% the free occurrence of $y$ before the $\beta$-reduction would become bound after the $\beta$-reduction step. A renaming of bound variables avoids such a capture: in this example, one can take an $\alpha$-equivalent%\footnote{A formal definition of this notion will be given later in this section.}% term, say $(\lambda_z.x\ z)$, and perform the $\beta$-step correctly as $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \lambda_z.y\ z$. Renaming of variables in the nominal setting is done via a name-swapping, which is formally defined at the level of variables as follows:

$\vswap{x}{y}{z} := \left\{ \begin{array}{ll}
y, & \mbox{ if } z = x; \\
x, & \mbox{ if } z = y; \\
z, & \mbox{ otherwise. } \\
\end{array}\right.$

This notion can be extended to the level of terms in a straightforward way:

%\begin{equation}\label{def:swap}
\swap{x}{y}{t} := \left\{ \begin{array}{ll}
\vswap{x}{y}{z}, & \mbox{ if } t = z; \\
\lambda_{\vswap{x}{y}{z}}.\swap{x}{y}{t_1}, & \mbox{ if } t = \lambda_z.t_1; \\
\swap{x}{y}{t_1}\ \swap{x}{y}{t_2}, & \mbox{ if } t = t_1\ t_2\\
\end{array}\right.
\end{equation}%

In the previous example, the variable capture can be avoided by applying a swap to the body of the abstraction before performing the metasubstitution: $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \metasub{(\swap{y}{z}{(\lambda_y.x\ y)})}{x}{y} = \metasub{(\lambda_z.x\ z)}{x}{y} = \lambda_z.y\ z$. The metasubstitution can be defined in different ways; in our formalization, it is defined as follows:

%\begin{equation}\label{msubst}
\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  t, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_x.t_1, & \mbox{ if } t = \lambda_x.t_1; \\
  \lambda_z.(\metasub{(\swap{y}{z}{t_1})}{x}{u}), & \mbox{ if } t = \lambda_y.t_1, x \neq y \\ & \mbox{ and } \\ & z\notin fv(t\ u) \cup \{x\}.
 \end{array}\right.
\end{equation}%
*)

(*
In what follows, we will adopt a mixed-notation approach, intertwining metanotation with the equivalent Coq notation. This strategy aids in elucidating the proof steps of the upcoming lemmas, enabling a clearer and more detailed comprehension of each stage in the argumentation. The corresponding Coq code for the swapping of variables, named [vswap], is defined as follows: *) 
(* begin hide *)
Definition vswap (x:atom) (y:atom) (z:atom) := if (z == x) then y else if (z == y) then x else z.

Lemma vswap_id: forall x y, vswap x x y = y.
Proof.
  intros. unfold vswap. case (y == x); intros; subst; reflexivity. 
Qed.

Lemma vswap_in: forall x y z, vswap x y z = x \/ vswap x y z = y \/  vswap x y z = z.
Proof.
  intros x y z. unfold vswap. default_simp.
Qed.

Lemma vswap_eq: forall x y z w, vswap x y z = vswap x y w <-> z = w.
Proof.
  intros x y z w; split.
  - unfold vswap. default_simp.
  - intro H; subst. reflexivity.
Qed.

Lemma vswap_neq: forall x y z w, z <> w <-> vswap x y z <> vswap x y w.
Proof.
  intros x y z w; split.
  - intros Hneq Heq. apply vswap_eq in Heq. contradiction.
  - intros Hneq Heq. subst. contradiction.
Qed.

Lemma vswap_id': forall x y, vswap x y x = y.
Proof.
  intros x y. unfold vswap. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma vswap_id'': forall x y, vswap x y y = x.
Proof.
  intros x y. unfold vswap. rewrite eq_dec_refl. case (y == x) eqn: Hyx.
  - assumption.
  - reflexivity.
Qed.

Lemma vswap_not: forall x y z, x <> z -> y <> z -> vswap x y z = z.
Proof.
  intros x y z H1 H2. unfold vswap. default_simp.
Qed.
Lemma vswap_equivariance : forall v x y z w, vswap x y (vswap z w v) = vswap (vswap x y z) (vswap x y w) (vswap x y v).
Proof.
  intros; unfold vswap; case(v == z); case (w == x); default_simp.
Qed.
(* end hide *)

(** ** An Explicit Substitution Operator *)

(** In this section, we extend the grammar (%\ref{lambda:grammar}%) with a new constructor called an explicit substitution operator:

%\begin{equation}\label{es:grammar}
  t ::= x \mid \lambda_x.t \mid t\ t \mid \esub{t}{x}{u}
\end{equation}%
%\noindent% where $\esub{t}{x}{u}$ represents a term with a pending substitution that will be evaluated by specific rules of a substitution calculus. The intended meaning of the explicit substitution is that it simulates the metasubstitution. This formalization aims to be a generic framework applicable to any calculus with explicit substitutions using a named notation for variables. Therefore, we do not fix rules for how the metasubstitution is to be simulated, but it is important to keep in mind that this is not a trivial task, since one can easily lose important properties of the original $\lambda$-calculus in the process %\cite{melliesTypedLcalculiExplicit1995,guillaumeCalculusDoesNot2000}%.

Calculi with explicit substitutions are formalisms that deconstruct the metasubstitution operation into finer-grained steps, thereby functioning as an intermediary between the $\lambda$-calculus and its practical implementations: they shed light on the execution models of higher-order languages. In fact, developing a calculus with explicit substitutions that is faithful to the $\lambda$-calculus, in the sense of preserving some of its desired properties, has been the main motivation behind the long list of calculi with explicit substitutions invented over the last decades %\cite{abadiExplicitSubstitutions1991,roseExplicitSubstitutionNames2011,benaissaLnCalculusExplicit1996,curienConfluencePropertiesWeak1996,munozConfluencePreservationStrong1996,kamareddineExtendingLcalculusExplicit1997a,blooExplicitSubstitutionEdge1999,davidLambdacalculusExplicitWeakening2001,kesnerTheoryExplicitSubstitutions2009a}%.

The following inductive definition corresponds to the grammar (%\ref{es:grammar}%), where the explicit substitution constructor, named [n_sub], has a special notation. Instead of writing [n_sub t x u], we will write [[x := u] t] similarly to (%\ref{es:grammar}%). Accordingly, [n_sexp] denotes the set of nominal $\lambda$-expressions equipped with an explicit substitution operator, which, for simplicity, we will refer to as just "terms". *)

Inductive n_sexp : Set :=
| n_var (x:atom)
| n_abs (x:atom) (t:n_sexp)
| n_app (t1:n_sexp) (t2:n_sexp)
| n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).
(* begin hide *)
Notation "[ x := u ] t" := (n_sub t x u) (at level 60).
(* end hide *)

(** A term is [pure] if it has no explicit substitution operator. The [size] of a term and its set of free variables [fv_nom] are defined as usual.
*)
(* begin hide *)
Inductive pure : n_sexp -> Prop :=
 | pure_var : forall x, pure (n_var x)
 | pure_app : forall e1 e2, pure e1 -> pure e2 -> pure (n_app e1 e2) 
 | pure_abs : forall x e1, pure e1 -> pure (n_abs x e1).

Fixpoint size (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  | n_sub t1 x t2 => 1 + size t1 + size t2
  end.

Lemma n_sexp_size: forall t, size t > 0.
Proof.
  induction t.
  - simpl. auto.
  - simpl. auto.
  - simpl. lia.
  - simpl. lia.
Qed.    

Fixpoint swap (x:atom) (y:atom) (t:n_sexp) : n_sexp :=
  match t with
  | n_var z     => n_var (vswap x y z)
  | n_abs z t1  => n_abs (vswap x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  | n_sub t1 z t2 => n_sub (swap x y t1) (vswap x y z) (swap x y t2)
  end.

Lemma swap_id : forall t x, swap x x t = t.
Proof.
  induction t; simpl; unfold vswap; default_simp.
Qed.

Lemma swap_size_eq : forall x y t, size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.

Lemma swap_symmetric : forall t x y, swap x y t = swap y x t.
Proof.
  induction t.
  - intros x' y. simpl. unfold vswap. default_simp.
  - intros x' y; simpl. unfold vswap. default_simp.
  - intros x y; simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  - intros. simpl. unfold vswap. default_simp.
Qed.

Lemma swap_symmetric_2: forall x y x' y' t,
    x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  intros. induction t; simpl in *; unfold vswap in *; default_simp.
Qed.

Lemma swap_comm: forall t x y x' y', x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  induction t; simpl in *; unfold vswap in *; default_simp.
Qed.

Lemma swap_involutive : forall t x y, swap x y (swap x y t) = t.
Proof.
 induction t; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma shuffle_swap : forall w y z t, w <> z -> y <> z -> (swap w y (swap y z t)) = (swap w z (swap w y t)).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma shuffle_swap' : forall w y n z, w <> z -> y <> z -> (swap w y (swap y z n)) = (swap z w (swap y w n)).
Proof.
  induction n; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma swap_equivariance : forall t x y z w, swap x y (swap z w t) = swap (vswap x y z) (vswap x y w) (swap x y t).
Proof.
  induction t.
  - intros. unfold vswap. case (z == x0).
    + case (w == x0).
       * intros. rewrite swap_id. rewrite e; rewrite e0. rewrite swap_id. reflexivity.
       * intros. case (w == y).
         ** intros. rewrite swap_symmetric. rewrite e; rewrite e0. reflexivity.
         ** intros. unfold swap. unfold vswap. default_simp.
    + unfold swap. unfold vswap. intros. default_simp.
  - intros. simpl. rewrite IHt. unfold vswap. case (x == z).
    + case (w == x0); default_simp.
    + case (w == x0).
      * default_simp.
      * intros. case (x == w); intros; case (z == x0); default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - intros. simpl. rewrite IHt1. rewrite IHt2. unfold vswap. default_simp.    
Qed.

Lemma pure_swap : forall x y t, pure t -> pure (swap x y t).
Proof.
  intros x y t H. induction H.
  - simpl. unfold vswap. case (x0 == x); case (x0 == y); intros; subst; apply pure_var.
  - simpl. apply pure_app; assumption.
  - simpl. unfold vswap. case (x0 == x); case (x0 == y); intros; subst; apply pure_abs; assumption.
Qed.

Lemma pure_swap_2: forall t x y, pure (swap x y t) -> pure t.
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y Hpure. apply pure_var.
  - intros x y Hpure. apply pure_abs. simpl in Hpure. inversion Hpure; subst. apply IHt1 with x y. assumption.
  - intros x y Hpure. apply pure_app.
    + simpl in Hpure. inversion Hpure; subst. apply IHt1 with x y. assumption.
    + simpl in Hpure. inversion Hpure; subst. apply IHt2 with x y. assumption.
  - intros x y Hpure. simpl in Hpure. inversion Hpure.
Qed.

Fixpoint fv_nom (t : n_sexp) : atoms :=
  match t with
  | n_var x => {{x}}
  | n_abs x t1 => remove x (fv_nom t1)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  | n_sub t1 x t2 => (remove x (fv_nom t1)) `union` fv_nom t2
  end.

Lemma notin_fv_nom_swap : forall z y t, z `notin` fv_nom t -> y `notin` fv_nom (swap y z t).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma notin_fv_nom_swap_2 : forall z y t, z `notin` fv_nom (swap y z t) -> y `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold vswap in H; default_simp.
Qed.
(* Lemma notin_fv_nom_swap_2 : forall z y t, z `notin` fv_nom (swap y z t) -> y `notin` fv_nom t.
Proof.
  intros z y t Hnotin. induction t; simpl in *; unfold vswap in Hnotin; default_simp.
Qed. *)

Lemma notin_fv_nom_swap_remove: forall t x y z, x <> y ->  x <> z -> x `notin` fv_nom (swap z y t) -> x `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold vswap in *; default_simp.
Qed.
(* Lemma notin_fv_nom_swap_remove: forall t x y z, x <> y ->  x <> z -> x `notin` fv_nom (swap z y t) -> x `notin` fv_nom t.
Proof.
  intros t x y z Hxy Hxz Hnotin. induction t; simpl in *; unfold vswap in *; default_simp.
Qed. *)

Lemma notin_fv_nom_swap_neq: forall t x y z, x <> y ->  x <> z -> x `notin` fv_nom t -> x `notin` fv_nom (swap z y t).
  Proof.
    induction t; simpl in *; unfold vswap; default_simp.
  Qed.

Lemma notin_fv_nom_remove_swap_inc: forall t x y, y `notin` fv_nom t -> x `notin` fv_nom (swap x y t).
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y Hnotin. simpl in *. apply notin_singleton_1 in Hnotin. unfold vswap. case (z == x) eqn: Hzx.
    + subst. apply notin_singleton. symmetry. assumption.
    + case (z == y) eqn: Hzy.
      * contradiction.
      * apply notin_singleton. assumption.
  - intros x y Hnotin. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. unfold vswap. case (y == x) eqn: Hyx.
      * subst. apply notin_remove_3. reflexivity.
      * rewrite eq_dec_refl. apply notin_remove_3. reflexivity.
    + unfold vswap. case (z == x) eqn: Hzx.
      * apply notin_remove_2. apply IHt1; assumption.
      * case (z == y) eqn: Hzy.
        ** apply notin_remove_3. reflexivity.
        ** apply notin_remove_2. apply IHt1; assumption.
  - intros x y Hnotin. simpl in *. apply notin_union.
    + apply IHt1. apply notin_union_1 in Hnotin. assumption.
    + apply IHt2. apply notin_union_2 in Hnotin. assumption.
  - intros x y Hnotin. simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
      * subst. unfold vswap. case (y == x) eqn: Hyx.
        ** subst. apply notin_remove_3. reflexivity.
        ** rewrite eq_dec_refl. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. apply IHt1; assumption.
    + apply notin_union_2 in Hnotin. apply IHt2; assumption.
Qed.
  
(* Lemma fv_nom_remove_swap_inc: forall t x y, x <> y -> y `notin` fv_nom t -> x `notin` fv_nom (swap x y t).
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y Hneq Hnotin. simpl in *. apply notin_singleton_1 in Hnotin. unfold vswap. destruct (z == x).
    + apply notin_singleton. symmetry. assumption.
    + destruct (z == y).
      * contradiction.
      * apply notin_singleton. assumption.
  - intros x y Hneq Hnotin. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. unfold vswap. destruct (y == x).
      * symmetry in e. contradiction.
      * rewrite eq_dec_refl. apply notin_remove_3. reflexivity.
    + unfold vswap. destruct (z == x).
      * apply notin_remove_2. apply IHt1; assumption.
      * destruct (z == y).
        ** apply notin_remove_3. reflexivity.
        ** apply notin_remove_2. apply IHt1; assumption.
  - intros x y Hneq Hnotin. simpl in *. apply notin_union.
    + apply IHt1.
      * assumption.
      * apply notin_union_1 in Hnotin; assumption.
    + apply IHt2.
      * assumption.
      * apply notin_union_2 in Hnotin. assumption.
  - intros x y Hneq Hnotin. simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
      * subst. unfold vswap. destruct (y == x).
        ** symmetry in e. contradiction.
        ** rewrite eq_dec_refl. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. apply IHt1; assumption.
    + apply notin_union_2 in Hnotin. apply IHt2; assumption.
Qed. *)

(* Induction Principles *)

Lemma strong_induction: forall (P:nat->Prop), (forall n, (forall m, m < n -> P m) -> P n) -> (forall n, P n).
Proof.
  intros Q IH n.
  assert (H := nat_ind (fun n => (forall m : nat, m < n -> Q m))).
  apply IH. apply H.
  - intros m Hlt; inversion Hlt.
  - intros n' H' m Hlt. apply IH. intros m0 Hlt'. apply H'. lia. 
Qed.

(* The standard proof strategy used so far is induction on the structure of terms. Nevertheless, the builtin induction principle automatically generated in Coq for the inductive definition [n_sexp] is not strong enough due to swappings:

<<
forall P :n_sexp -> Prop,
 (forall x:atom, P(n_var x)) ->
 (forall (x:atom) (t:n_sexp), P t -> P(n_abs x t)) ->
 (forall t1:n_sexp, P t1 -> forall t2:n_sexp, P t2 -> P(n_app t1 t2)) ->
 (forall t1:n_sexp, P t1 -> forall (x:atom) (t2:n_sexp), P t2 -> P([x:=t2]t1)) ->
       forall t:n_sexp, P t
>>

In fact, in general, the induction hypothesis in the abstraction case (resp. explicit substitution case) refers to the body [t] of the abstraction (resp. [t1] of the explicit substitution), while the goal involves a swap acting on the body of the abstraction (resp. explicit substitution). In order to circumvent this problem, we defined a customized induction principle based on the size of terms: *)

Lemma n_sexp_induction: forall P : n_sexp -> Prop, (forall x, P (n_var x)) ->
 (forall t1 z, (forall t2 x y, size t2 = size t1 -> P (swap x y t2)) -> P (n_abs z t1)) ->
 (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
 (forall t1 t3 z, P t3 -> (forall t2 x y, size t2 = size t1 -> P (swap x y t2)) -> P (n_sub t1 z t3)) -> (forall t, P t).
Proof.
  intros P Hvar Habs Happ Hsub t. remember (size t) as n. generalize dependent t. induction n using strong_induction. intro t; case t.
  - intros x Hsize. apply Hvar.
  - intros x t' Hsize. apply Habs. intros t'' x1 x2 Hsize'. apply H with (size t'').
    + rewrite Hsize'. rewrite Hsize. simpl. apply Nat.lt_succ_diag_r.
    + symmetry. apply swap_size_eq.
  - intros. apply Happ.
    + apply H with ((size t1)).
      ++ simpl in Heqn. rewrite Heqn. lia. 
      ++ reflexivity.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn. lia. 
      ++ reflexivity.
  - intros. apply Hsub.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn. lia. 
      ++ reflexivity.
    + intros. apply H with ((size (swap x0 y t0))).
      ++ rewrite swap_size_eq. rewrite H0. simpl in Heqn. rewrite Heqn. lia. 
      ++ reflexivity.
Qed. 
(* %\noindent% which states that in order to conclude that a certain property $P$ holds for all terms, we need to prove that:
%\begin{enumerate}
 \item $P$ must hold for any variable;
 \item If $P$ holds for the term $\swap{x}{y}{t_2}$, where $t_1$ and $t_2$ have the same size, then it also holds for the abstraction $\lambda_z.t_1,\forall x, y, z, t_1$ and $t_2$;
 \item If $P$ holds for the terms $t_1$ and $t_2$ the it also holds for the application $t_1\ t_2$;
 \item If $P$ holds for the term $t_3$ and for the term $\swap{x}{y}{t_2}$, where $t_1$ and $t_2$ have the same size, then it also holds for the explicit substitution $\esub{t_1}{z}{t_3},\forall x, y, z, t_1, t_2$ and $t_3$.
\end{enumerate}%

The following lemma is a first example of the use of the [n_sexp_induction] principle: *)  

Lemma notin_fv_nom_equivariance: forall t x' x y, x' `notin` fv_nom t -> vswap x y x'  `notin` fv_nom (swap x y t).
Proof.
  induction t as [z | t1 z | t1 t2 | t1 t2 z ] using n_sexp_induction. 
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. apply vswap_neq. assumption. 
  - intros x' x y Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv. 
    + subst. apply notin_remove_3. reflexivity. 
    + apply notin_remove_2. specialize (H t1 x x). rewrite swap_id in H. apply H. 
      * reflexivity.
      * assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply IHt2. apply notin_union_1 in Hfv. assumption.
    + apply IHt1. apply notin_union_2 in Hfv. assumption. 
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv. 
      * subst. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. specialize (H t1 x x). rewrite swap_id in H. apply H.
        ** reflexivity.
        ** assumption.
    + apply notin_union_2 in Hfv. apply IHt1; assumption. 
Qed.
(* %\noindent{\bf Proof.}% Note that in the paper and pencil notation, this lemma states that: %\newline%

If $x' \notin fv\_nom(t)$ then $\vswap{x}{y}{x'} \notin fv\_nom(\swap{x}{y}{t})$.%\newline%

%\noindent% The proof is by induction on the size of the term $t$.
%\begin{enumerate} \item If $t$ is a variable, say $z$, then $x' \neq z$ by hypothesis, and we need to prove that $\vswap{x}{y}{x'} \neq \vswap{x}{y}{z}$. We conclude by lemma $swap\_neq$. \item If is an abstraction, say $t = \lambda_z. t_1$, then we have by induction hypothesis that if $x' \notin \swap{x}{y}{t_2}$ then $\vswap{x_0}{y_0}{x'} \notin \swap{x_0}{y_0}{\swap{x}{y}{t_2}}$ for any term $t_2$ with the same size as $t_1$, and any variables $x, y, x_0$ and $y_0$. At this point is important to notice that an structural induction would generate an induction hypothesis with $t_1$ only, which is not strong enough to prove the goal $\vswap{x}{y}{x'} \notin fv\_nom(\swap{x}{y}{\lambda_z. t_1})$ that has $\swap{x}{y}{t_1}$ (and not $t_1$ alone!) after the propagation of the swap. In addition, we have by hypothesis that $x' \notin fv\_nom(t_1) \backslash \{z\}$. This means that either $x' = z$ or $x' \notin fv\_nom(t_1)$, and there are two subcases: \begin{enumerate} \item If $x' = z$ then the goal is $\vswap{x}{y}{z} \notin fv\_nom(\swap{x}{y}{\lambda_z. t_1}) \Leftrightarrow$ $\vswap{x}{y}{z} \notin fv\_nom(\lambda_{\vswap{x}{y}{z}}. \swap{x}{y}{t_1}) \Leftrightarrow$\newline $\vswap{x}{y}{z} \notin fv\_nom(\swap{x}{y}{t_1})\backslash \{\vswap{x}{y}{z}\}$ we are done by lemma $notin\_remove\_3$.\footnote{This is a lemma from Metalib library and it states that {\tt forall (x y : atom) (s : atoms), x = y -> y `notin` remove x s}.} \item Otherwise, $x' \notin fv\_nom(t_1)$, and we conclude using the induction hypothesis taking $x_0=x$, $y_0=y$ and the universally quantified variables $x$ and $y$ of the internal swap as the same variable (it does not matter which one). \end{enumerate} \item The application case is straightforward from the induction hypothesis. \item The case of the explicit substitution, {\it i.e.} when $t = \esub{t_1}{z}{t_2}$, we have to prove that $\vswap{x}{y}{x'} \notin fv\_nom(\swap{x}{y}{(\esub{t_1}{z}{t_2})})$. We then propagate the swap over the explicit substitution operator and show, by the definition of $fv\_nom$, we have to prove that both $\vswap{x}{y}{x'} \notin (fv\_nom (\swap{x}{y}{t_1}))\backslash \{\vswap{x}{y}{z}\}$ and $\vswap{x}{y}{x'} \notin fv\_nom (\swap{x}{y}{t_2})$. \begin{enumerate} \item In the former case, the hypothesis $x' \notin fv\_nom(t_1)\backslash \{z\}$ generates two subcases, either $x' = z$ or $x'\notin fv\_nom(t_1)$, and we conclude with the same strategy of the abstraction case. \item The later case is straightforward by the induction hypothesis. $\hfill\Box$ \end{enumerate}\end{enumerate}%*)

(* The other direction is also true, but we skip the proof that is also by induction on the size of term [t]:*)

Lemma notin_fv_nom_remove_swap: forall t x y z, vswap x y z `notin` fv_nom (swap x y t) -> z `notin` fv_nom t.
Proof.
  induction t as [w | t1 w IH | t1 t2 IH1 IH2 | t1 t2 w IH2 IH1 ] using n_sexp_induction.
  - intros x y z Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. apply vswap_neq in Hfv. assumption.
  - intros x y z Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv.
    + apply vswap_eq in H. subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. replace t1 with (swap x x t1).
      * apply IH with x y.
        ** reflexivity.
        ** rewrite swap_id. assumption.
      * apply swap_id.
  - intros x y z Hfv. simpl in *. apply notin_union.
    + apply IH1 with x y. apply notin_union_1 in Hfv. assumption.
    + apply IH2 with x y. apply notin_union_2 in Hfv. assumption.
  - intros x y z Hfv. simpl in *. apply notin_union.
    + apply notin_union_1 in Hfv. case (z == w).
      * intro Heq. subst. apply notin_remove_3. reflexivity.
      * intro Hneq. apply notin_remove_1 in Hfv. destruct Hfv.
        ** apply vswap_eq in H. symmetry in H. contradiction.
        ** specialize (IH1 t1 x x). rewrite swap_id in IH1. apply notin_remove_2. apply IH1 with x y.
           *** reflexivity.
           *** assumption.
    + apply IH2 with x y. apply notin_union_2 in Hfv. assumption.
Qed.        

Lemma swap_remove_reduction: forall x y t, remove x (remove y (fv_nom (swap y x t))) [=] remove x (remove y (fv_nom t)).
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - rewrite remove_symmetric. simpl. unfold vswap. default_simp.
    + repeat rewrite remove_singleton_empty. repeat rewrite remove_empty. reflexivity.
    + rewrite remove_symmetric. rewrite remove_singleton_empty. rewrite remove_symmetric. rewrite remove_singleton_empty. repeat rewrite remove_empty. reflexivity.
    + rewrite remove_symmetric. reflexivity.
  - simpl. unfold vswap. default_simp.
    + rewrite double_remove. rewrite remove_symmetric. rewrite double_remove. rewrite remove_symmetric. assumption.
    + rewrite double_remove. symmetry. rewrite remove_symmetric. rewrite double_remove. rewrite remove_symmetric. symmetry. assumption.
    + assert (remove y (remove z (fv_nom (swap y x t1))) [=] remove z (remove y (fv_nom (swap y x t1)))). {
         rewrite remove_symmetric. reflexivity.
       }
       assert (remove y (remove z (fv_nom t1)) [=] remove z (remove y (fv_nom t1))). {
         rewrite remove_symmetric. reflexivity.
       }
       rewrite H; rewrite H0. rewrite remove_symmetric. symmetry. rewrite remove_symmetric. rewrite IHt1. reflexivity.       
  - simpl. repeat rewrite remove_union_distrib. apply Equal_union_compat; assumption.
  - simpl. unfold vswap. default_simp.
    + repeat rewrite remove_union_distrib. apply Equal_union_compat.
      * rewrite remove_symmetric. rewrite double_remove. rewrite double_remove. rewrite remove_symmetric. assumption.
      * assumption.
    + repeat rewrite remove_union_distrib. apply Equal_union_compat.
      * rewrite double_remove. symmetry. rewrite remove_symmetric. rewrite double_remove. rewrite remove_symmetric. symmetry. assumption.
      * assumption.
    + repeat rewrite remove_union_distrib. apply Equal_union_compat.
      * assert (remove y (remove z (fv_nom (swap y x t1))) [=] remove z (remove y (fv_nom (swap y x t1)))). {
         rewrite remove_symmetric. reflexivity.
           }
           assert (remove y (remove z (fv_nom  t1)) [=] remove z (remove y (fv_nom t1))). {
         rewrite remove_symmetric. reflexivity.
           }
           rewrite H; rewrite H0. rewrite remove_symmetric. symmetry. rewrite remove_symmetric. symmetry. rewrite IHt1. reflexivity.
      * assumption.
Qed.

Lemma remove_fv_swap: forall x y t, x `notin` fv_nom t -> remove x (fv_nom (swap y x t)) [=] remove y (fv_nom t).
Proof. (** %\noindent {\bf Proof.}% The proof is by induction on the structure of [t].%\newline% *)
  intros x y t. induction t.
  (** %\noindent%$\bullet$ The first case is when [t] is a variable, say [x0]. By hypothesis [x0 <> x], and we need to show that [remove x (fv_nom (swap y x x0)) [=] remove y (fv_nom x0)]. There are two cases to consider: *)
  - intro Hfv. simpl in *. apply notin_singleton_1 in Hfv. unfold vswap. case (x0 == y).
    (** If [x0 = y] then both sides of the equality are the empty set, and we are done. *)
    + intro Heq. subst. apply remove_singleton.
    (** If [x0 <> y] then we are also done because both sets are equal to the singleton containing [x0].%\newline% *)
    + intro Hneq. case (x0 == x).
      * intro Heq. contradiction.
      * intro Hneq'. rewrite AtomSetProperties.remove_equal.
        ** rewrite AtomSetProperties.remove_equal.
           *** reflexivity.
           *** apply notin_singleton_2; assumption.
        ** apply notin_singleton_2; assumption.
  (** %\noindent% $\bullet$ If [t] is an abstraction, say [n_abs x0 t] then *)
  - intros Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv.
    + subst. assert (H: vswap y x x = y).
      {
        unfold vswap. destruct (x == y).
        - assumption.
        - rewrite eq_dec_refl. reflexivity.
      }
      rewrite H. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
    + unfold vswap. destruct (x0 == y).
      * subst. repeat rewrite double_remove. apply IHt. assumption.
      * destruct (x0 == x).
        ** subst. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
        ** rewrite remove_symmetric. assert (Hr: remove y (remove x0 (fv_nom t)) [=] remove x0 (remove y (fv_nom t))).
           {
           rewrite remove_symmetric. reflexivity.
           }
           rewrite Hr. clear Hr. apply AtomSetProperties.Equal_remove. apply IHt. assumption.
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    apply IHt1 in Hfv'. apply IHt2 in Hfv. pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (fv_nom (swap y x t1)) (fv_nom (swap y x t2)) x). specialize (H2 (fv_nom t1) (fv_nom t2) y). rewrite Hfv' in H1. rewrite Hfv in H1. rewrite H1. rewrite H2. reflexivity.
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (remove (vswap y x x0) (fv_nom (swap y x t1))) (fv_nom (swap y x t2)) x). rewrite H1.
    specialize (H2 (remove x0 (fv_nom t1)) (fv_nom t2) y). rewrite H2. apply Equal_union_compat.
    + unfold vswap. case (x0 == y); intros; subst.
      * unfold vswap in H1. rewrite eq_dec_refl in H1. rewrite double_remove in *. apply IHt2 in Hfv. case (x == y); intros; subst.
        ** repeat rewrite swap_id in *. rewrite double_remove. reflexivity.
        ** rewrite double_remove. apply IHt1. apply diff_remove_2 in Hfv'.
           *** assumption.
           *** assumption.
      * destruct (x0 == x).
        ** subst. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
        ** rewrite remove_symmetric. symmetry. rewrite remove_symmetric. apply AtomSetProperties.Equal_remove. symmetry. apply IHt1. apply diff_remove_2 in Hfv'.
            *** assumption.
            *** auto.
    + apply IHt2. apply Hfv.
Qed.

Lemma n_sexp_size_induction_P: forall P: n_sexp -> Prop,
  (forall x, (forall y, size y < size x -> P y) -> P x) -> forall z, P z.
Proof.
  intros P IH z. remember (size z) as n. generalize dependent z. induction n using strong_induction.
intro z. case z eqn:H'. 
  - intro H''. apply IH. intros y Hsize. simpl in Hsize. inversion Hsize; subst.
    + pose proof n_sexp_size as H2. specialize (H2 y). lia.
    + lia.
  - intro H''. apply IH. intros y Hsize. apply (H (size y)).
    + simpl in *. subst. assumption.
    + reflexivity.
  - intro H''. apply IH. intros y Hsize. apply (H (size y)).
    + simpl in *. subst. assumption.
    + reflexivity.
  - intro H''. apply IH. intros y Hsize. apply (H (size y)).
    + simpl in *. subst. assumption.
    + reflexivity.
Qed.

Lemma n_sexp_size_induction: forall P : n_sexp -> Prop, (forall x, P (n_var x)) ->
                                                     (forall t1 z, (forall t1', size t1' < size (n_abs z t1) -> P t1') -> P (n_abs z t1)) ->
                                                     (forall t1 t2, (forall t1', size t1' < size (n_app t1 t2) -> P t1') -> P (n_app t1 t2)) ->
                                                     (forall t1 t2 z, (forall t1', size t1' < size (n_sub t1 z t2) -> P t1') -> P (n_sub t1 z t2)) -> (forall t, P t).
Proof.
  intros P Hvar Habs Happ Hsub t. remember (size t) as n. generalize dependent t. induction n using strong_induction. intro t; case t.
  - intros x Hsize. apply Hvar.
  - intros x t' Hsize. apply Habs. intros t'' Hsize'. apply H with (size t'').
    + rewrite Hsize. simpl. auto.
    + reflexivity.
  - intros t1 t2 Hsize. apply Happ. intros t1' Hsize'. apply H with (size t1').
    + rewrite Hsize. assumption.
    + reflexivity.
  - intros t1 x t2 Hsize. simpl in *. apply Hsub. intros t1' Hsize'. apply H with (size t1').
    + rewrite Hsize. assumption.
    + reflexivity.
Qed.

Definition Rel (A: Type) := A -> A -> Prop.

Inductive ctx  (R : Rel n_sexp): Rel n_sexp :=
 | step_redex: forall (t1 t2: n_sexp), R t1 t2 -> ctx R t1 t2
 | step_n_abs: forall (t1 t2: n_sexp) (x: atom), ctx R t1 t2 -> ctx R (n_abs x t1) (n_abs x t2)
 | step_n_app_left: forall (t1 t1' t2: n_sexp) , ctx R t1 t1' -> ctx R (n_app t1 t2) (n_app t1' t2)
 | step_n_app_right: forall (t1 t2 t2': n_sexp) , ctx R t2 t2' -> ctx R (n_app t1 t2) (n_app t1 t2')
 | step_n_sub_out: forall (t1 t1' t2: n_sexp) (x : atom) , ctx R t1 t1' -> ctx R ([x := t2]t1) ([x := t2]t1')
 | step_n_sub_in: forall (t1 t2 t2': n_sexp) (x:atom), ctx R t2 t2' -> ctx R ([x := t2]t1) ([x := t2']t1).

Lemma n_sexp_induction_ctx: forall (R: Rel n_sexp) (P : n_sexp -> n_sexp -> Prop), (forall t1 t2 : n_sexp, R t1 t2 -> P t1 t2) -> 
       (forall (t1 t2 : n_sexp) (x: atom), ctx R t1 t2 -> (forall t1' t2', size t1' = size t1 -> size t2' = size t2 -> ctx R t1' t2' -> P t1' t2') -> P (n_abs x t1) (n_abs x t2)) ->
       (forall t1 t1' t2 : n_sexp, ctx R t1 t1' -> P t1 t1' -> P (n_app t1 t2) (n_app t1' t2)) ->
       (forall t1 t2 t2' : n_sexp, ctx R t2 t2' -> P t2 t2' -> P (n_app t1 t2) (n_app t1 t2')) ->
       (forall (t1 t1' t2 : n_sexp) (x: atom), ctx R t1 t1' -> (forall t1'' t1''', size t1'' = size t1 -> size t1''' = size t1' -> ctx R t1'' t1''' -> P t1'' t1''') -> P ([x := t2] t1) ([x := t2] t1')) ->
       (forall (t1 t2 t2' : n_sexp) (x y: atom), ctx R t2 t2' -> P t2 t2' -> P ([x := t2] t1) ([y := t2'] t1)) ->
       forall t1 t2 : n_sexp, ctx R t1 t2 -> P t1 t2.
Proof.
  intros R P H Habs Happ_left Happ_right Hsub_out Hsub_in t1 t2 Hctx. remember (size t1 + size t2) as n. generalize dependent t2. generalize dependent t1. induction n using strong_induction. intros t1 t2 Hctx Hsize. induction Hctx.
  - apply H. assumption.
  - apply Habs.
    + assumption.
    + intros t1' t2' Hsize1 Hsize2 Hbeta'. apply H0 with (size t1 + size t2).
      * rewrite Hsize. simpl. lia.
      * assumption.
      * rewrite Hsize1. rewrite Hsize2. reflexivity.
  - apply Happ_left.
    + assumption.
    + apply H0 with (size t1 + size t1').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
  - apply Happ_right.
    + assumption.
    + apply H0 with (size t2 + size t2').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
  - apply Hsub_out.
    + assumption.
    + intros t1'' t1''' Hsize1 Hsize2 Hbeta'. apply H0 with (size t1'' + size t1''').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
  - apply Hsub_in.
    + assumption.
    + apply H0 with (size t2 + size t2').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
Qed.
(* end hide *)
