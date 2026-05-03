From Coq Require Import Arith List Lia.
Import ListNotations.

Fixpoint sorted (l:list nat): Prop :=
  match l with
    [] => True
  | x::l1 => x <=hd x l1 /\ sorted l1
  end.

Fixpoint insert x l :=
  match l with
    [] => [x]
  | y::l => if le_dec x y then x ::y::l else y::insert x l
  end.
  
  Check hd.

(* TODO
  destruct sur l, destruct sur la condition d'un if
  *)
Lemma sorted_le: forall l, sorted l -> 
  forall a, a <= hd a l -> forall x, a < x -> a <= hd a (insert x l).
Proof.
  intros l Hsorted a Ha x Hx.
  destruct l as [| y l'].
  - simpl.
    lia.
  - simpl.
    destruct (le_dec x y).
    -- simpl.
       lia.
    -- simpl.
       simpl in Ha. 
       apply Ha.
Qed.

(* TODO
  - induction sur l
  - destruct sur condition d'un if
  - utiliser (apply) sorted_le
  - lia pour l'arithmétique
*)
Lemma insert_sorted: forall l, sorted l -> forall x, sorted (insert x l).
Proof.
Admitted.

Fixpoint sort l :=
  match l with
    [] => []
  | x::l => insert x (sort l)
  end.

(* TODO
  - induction sur l
  - utiliser insert_sorted
*)
Theorem sort_sorted: forall l, sorted (sort l).
Proof.
Admitted.

(**************************************************************)

Fixpoint split (l : list nat) :=
  match l with
  | [] => ([], [])
  | x::l => let (l1,l2) := split l in (x::l2,l1)
  end.

Lemma split_example : split [1; 2; 3; 4; 5] = ([1; 3; 5], [2; 4]).
Proof.
reflexivity.
Qed.

(* TODO
  - induction sur l
  - injection H en présence de H: (_,_) = split _
  - subst en présence de H:variable = ...
  - destruct (split l)  as [ll1 ll2] lorsque l n'apparait que dans (split l)
  - injection H en présence de H:(_,_)=(_,_)
  - rewrite Nat.add_comm pour la commutativité de l'addition
  - rewrite <-IHl pour appliquer l'hypothèse d'induction de droite à gauche
*)
Lemma length_split :
  forall l l1 l2, (l1,l2) = split l -> length l = length l1 + length l2.
Proof.
Admitted.

(*
  TODO
  - destruct l (pas d'induction)
  - destruct (split l) as [ll1 ll2] en présence de let (l1,l2):=split l in ...
  - injection H en présence de H:(_,_)=(_,_)
  - discriminate en présence du but _::_ <> []
*)

Lemma split_nel :
  forall l l1 l2, (l1,l2) = split l -> length l > 1 -> l1 <> [].
Proof.
Admitted.

(* TODO
  mêmes consignes + utiliser lia sur de l'arithmétique
*)
Lemma split_ner :
  forall l l1 l2, (l1,l2) = split l -> length l > 1 -> l2 <> [].
Proof.
Admitted.

Fixpoint merge (xs:list nat) : list nat -> list nat := 
  match xs with 
    | nil => fun ys => ys
    | (x::xs') => 
      (fix inner_merge (ys:list nat) : list nat := 
         match ys with 
           | nil => x::xs'
           | y::ys' => if le_dec x y then 
                         x :: (merge xs' (y::ys'))
                       else 
                         y :: (inner_merge ys')
         end)
  end.

(* TODO
  preuve plus compliquée
    induction sur l1 puis dans le cas général induction sur l2
    ...
*)
Lemma merge_sorted: forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1.
  - simpl; auto.
  - simpl; induction l2; intros; auto.
Admitted.

Require Import Recdef.

Function msort l {measure length l} := 
  match l with
     [] => []
  | [x] => [x]
  | _ => let (l1,l2) := split l in merge (msort l1) (msort l2)
  end.
Proof.
  - intros.
     symmetry in teq1.
     generalize (split_nel _ _ _ teq1); intro.
     generalize (split_ner _ _ _ teq1); intro.
     apply length_split in teq1.
     simpl in *.
     assert (length l2 > 0).
     destruct l2; simpl in *; try lia.
     exfalso; apply H; auto with arith.
     lia.
  - intros.
     symmetry in teq1.
     generalize (split_nel _ _ _ teq1); intro.
     generalize (split_ner _ _ _ teq1); intro.
     apply length_split in teq1.
     simpl in *.
     assert (length l3 > 0).
     destruct l3; simpl in *; try lia.
     exfalso; apply H0; auto with arith.
     lia.
Qed.

(* TODO
  induction sur n
  compliqué...
*)
Lemma msort_sortedN: forall n, forall l, length l <= n -> sorted (msort l).
Proof.
  induction n; simpl; intros; auto.
  - destruct l; simpl in *; auto.
      -- rewrite msort_equation; simpl; auto.
      -- simpl in H; lia. 
  - rewrite msort_equation.
Admitted.

Theorem msort_sorted: forall l, sorted (msort l).
Proof.
  intro.
  apply (msort_sortedN (length l)); auto.
Qed.


