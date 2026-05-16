Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

(* Ce sujet a pour d'écrire de démontrer des propriétés de fonctions sur les expressions *)

(*********************************)
(* Le type des expressions (expr)  *)
(*********************************)

Inductive expr : Type :=
| Const : nat -> expr
| Var : nat -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr.

(******************
Un environnement est une liste de couples (no de variable, valeur)
******************)
(* renvoie la valeur de la variable x *)
Fixpoint lookup (x: nat) (env: list (nat * nat)) : nat :=
  match env with
  | [] => 0
  | (y,v)::env' => if Nat.eqb x y then v else lookup x env'
  end.

(******************************************************)
(* Évaluation d'une expression  dans un environnement      *)
(******************************************************)

Fixpoint eval (e: expr) (env: list (nat * nat)) : nat :=
  match e with
  | Const n => n
  | Var x => lookup x env
  | Add e1 e2 => eval e1 env + eval e2 env
  | Mul e1 e2 => eval e1 env * eval e2 env
  end.

(******************)
(* Fonctions           *)
(******************)

(* taille d'une expression *)
Fixpoint size (e: expr) : nat :=
  match e with
  | Const _ => 1
  | Var _ => 1
  | Add e1 e2 => 1 + size e1 + size e2
  | Mul e1 e2 => 1 + size e1 + size e2
  end.

(* nombre de variables d'une expression *)
Fixpoint nb_vars (e: expr) : nat :=
  match e with
  | Const _ => 0
  | Var _ => 1
  | Add e1 e2 => nb_vars e1 + nb_vars e2
  | Mul e1 e2 => nb_vars e1 + nb_vars e2
  end.

(* remplace la variable x par la valeur v dans l'expression e *)
Fixpoint subst (x: nat) (v: nat) (e: expr) : expr :=
  match e with
  | Const n => Const n
  | Var y => if Nat.eqb x y then Const v else Var y
  | Add e1 e2 => Add (subst x v e1) (subst x v e2)
  | Mul e1 e2 => Mul (subst x v e1) (subst x v e2)
  end.

(* supprime l'ajout de 0 ou le produit par 1 dans e *)
Fixpoint simplify (e: expr) : expr :=
  match e with
  | Add (Const 0) e2 => simplify e2
  | Add e1 (Const 0) => simplify e1
  | Mul (Const 1) e2 => simplify e2
  | Mul e1 (Const 1) => simplify e1
  | Add e1 e2 => Add (simplify e1) (simplify e2)
  | Mul e1 e2 => Mul (simplify e1) (simplify e2)
  | Const n => Const n
  | Var x => Var x
  end.

(* nombre d'opérations + ou * *)
Fixpoint nb_ops (e: expr) : nat :=
  match e with
  | Const _ => 0
  | Var _ => 0
  | Add e1 e2 => 1 + nb_ops e1 + nb_ops e2
  | Mul e1 e2 => 1 + nb_ops e1 + nb_ops e2
  end.

(* inverse les arguments de + et * *)
Fixpoint mirror_expr (e: expr) : expr :=
  match e with
  | Const n => Const n
  | Var x => Var x
  | Add e1 e2 => Add (mirror_expr e2) (mirror_expr e1)
  | Mul e1 e2 => Mul (mirror_expr e2) (mirror_expr e1)
  end.

(******************)
(* Exercices - la plupart des preuves se font par induction sur e *)
(******************)

(* TODO 0.5 pts *)
Lemma eval_var : forall x env, eval (Var x) env = lookup x env.
Proof.
firstorder.
Qed.

(* TODO 0.5 pts *)
Lemma eval_add : forall e1 e2 env, eval (Add e1 e2) env = eval e1 env + eval e2 env.
Proof.
firstorder.
Qed.

(* TODO 1 pt *)
Lemma size_ge_1 : forall e, size e >= 1.
Proof.
induction e; firstorder; simpl; lia.
Qed.

(* TODO 1 pt *)
Lemma nb_vars_le_size : forall e, nb_vars e <= size e.
Proof.
induction e; firstorder; simpl; lia.
Qed.

(* TODO 2.5 pt *)
(* utiliser "destruct (Nat.eqb_spec x y)" en présence de if x=?y ... *)
(* utiliser Nat.eqb_refl *)
Lemma eval_subst_cons : forall e x v env,
  eval (subst x v e) env = eval e ((x,v)::env).
Proof.
intros.
induction e; auto.
- simpl.
  destruct (Nat.eqb_spec x n).
  + subst.
    rewrite Nat.eqb_refl.
    easy.
  + rewrite <- Nat.eqb_neq in n0.
    rewrite Nat.eqb_sym.
    rewrite n0.
    easy.
- simpl.
  rewrite IHe1, IHe2.
  reflexivity.
- simpl.
  rewrite IHe1, IHe2.
  reflexivity.
Qed.

(* TODO 2 pts *)
(* utiliser "destruct (Nat.eqb_spec x y)" en présence de if x=?y ... *)
Lemma size_subst : forall x v e, size (subst x v e) = size e.
Proof.
intros.
induction e; firstorder; simpl.
- destruct (Nat.eqb_spec x n); easy.
- rewrite IHe1, IHe2.
  reflexivity.
- rewrite IHe1, IHe2.
  reflexivity.
Qed.

(* TODO 1.5 pts *)
(* pas d'induction *)
(* utiliser "destruct e" en présence de match e with ... *)
Lemma eval0: forall e e1 e2 env,
   eval (match e with
              Const 0 => e1
          | _ => e2
          end) env = 
    match e with
      Const 0 => eval e1 env
    | _ => eval e2 env
    end.
Proof.
destruct e; firstorder.
destruct n; firstorder.
Qed.

(* TODO 1.5 pt *)
(* pas d'induction *)
(* utiliser "destruct e" en présence de match e with ... *)
Lemma simpl0l: forall e1 v2 env,
    match e1 with
    | Const 0 => v2
    | _ => eval e1 env + v2
    end = eval e1 env + v2.
Proof.
destruct e1; firstorder.
destruct n; firstorder.
Qed.

(* non demandée *)
Lemma simpl0r: forall e2 v1 env,
    match e2 with
    | Const 0 => v1
    | _ => v1 + eval e2 env
    end = v1 + eval e2 env.
Proof.
intros.
destruct e2.
-destruct n.
--auto.
--auto.
-auto.
-auto.
-auto.
Qed.

(* TODO 1.5 pts *)
(* pas d'induction *)
(* utiliser "destruct e" en présence de match e with ... *)
Lemma eval1: forall e e1 e2 env,
   eval (match e with
              Const 1 => e1
          | _ => e2
          end) env = 
    match e with
      Const 1 => eval e1 env
    | _ => eval e2 env
    end.
Proof.
destruct e; firstorder.
destruct n; firstorder.
destruct n; firstorder.
Qed.

(*non demandée *)
Lemma simpl1l: forall e1 v2 env,
    match e1 with
    | Const 1 => v2
    | _ => eval e1 env * v2
    end = eval e1 env * v2.
Proof.
Admitted.

(* non demandée *)
Lemma simpl1r: forall e2 v1 env,
    match e2 with
    | Const 1 => v1
    | _ => v1 * eval e2 env
    end = v1 * eval e2 env.
Proof.
Admitted.

(* TODO 2.5 pts *)
(* induction sur e *)
(* utiliser eval0, eval1, simpl0l, simpl0r, simpl1r, simpl1l *)
Lemma simplify_preserves_eval : forall e env, eval (simplify e) env = eval e env.
Proof.
Admitted.

(* TODO 0.5 pts *)
Lemma nb_ops_le_size : forall e, nb_ops e <= size e.
Proof.
induction e; simpl; lia.
Qed.

(* TODO 2 pts *)
Lemma closed_eval_nil : forall e env, nb_vars e = 0 -> eval e env = eval e [] .
Proof.
intros.
induction e; firstorder; simpl.
- easy.
- rewrite IHe1, IHe2; firstorder; simpl in H; lia.
- rewrite IHe1, IHe2; firstorder; simpl in H; lia.
Qed.

(* TODO 2 pts *)
(* utiliser "destruct (x =? y) eqn:h" en présence de if (x=?y)... *)
Lemma subst_idempotent_same_var : forall x v w e,
  subst x v (subst x w e) = subst x w e.
Proof.
intros.
induction e; firstorder; simpl.
- destruct (x =? n) eqn:h; auto.
  simpl.
  rewrite h.
  reflexivity.
- rewrite IHe1, IHe2.
  reflexivity.
- rewrite IHe1, IHe2.
  reflexivity.
Qed.

(* TODO 2 pts *)
(* utiliser Nat.add_comm *)
Lemma mirror_eval_comm : forall e env, eval (mirror_expr e) env = eval e env.
Proof.
intros.
induction e; firstorder; simpl.
- rewrite IHe1, IHe2.
  apply Nat.add_comm.
- rewrite IHe1, IHe2.
  apply Nat.mul_comm.
Qed.