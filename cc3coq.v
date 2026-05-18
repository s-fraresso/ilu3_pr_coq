(*
  Ce sujet a pour but de manipuler des arbres de preuve de formules de logique des propositions.
  Le langage est limit\u00e9 \u00e0 3 op\u00e9rateurs: => , &, not
  
  Pour la bonne lecture des r\u00e8gles de preuve, changer la fonte
     Edit/Pr\u00e9f\u00e9rences/Fonts Courier New

  Certaines preuves contiennent 7 cas. Ces cas seront not\u00e9s s\u00e9paremment
    => bien les distinguer avec des "-"
       bien indenter les preuves (correction manuelle)
       marquer les sous-cas avec "+", le  3eme niveau avec "*", les suivants avec "**" ...
       terminer par "admit" les cas non ou partiellement trait\u00e9s
  Terminer par Qed une preuve compl\u00e8te
Remarque:
  - seuls les th\u00e9or\u00e8mes marqu\u00e9s TODO sont \u00e0 prouver
  - les points donnent une id\u00e9e (subjective) du niveau de difficult\u00e9 mais ne constituent pas un bar\u00e8me
  - il n'est pas attendu que vous fassiez toutes les preuves
  - toutes les tactiques sont autoris\u00e9es.

indications g\u00e9n\u00e9rales
  - en pr\u00e9sence de H:P/\Q  "destruct H"
  - en pr\u00e9sence de H:P\/Q  "destruct H"
  - en pr\u00e9sence de H:exists x, P x  "destruct H as [x H]"
  - en pr\u00e9sence de if c then ...    "destruct c"
  - en pr\u00e9sence de match c with ...    "destruct c"
  - en pr\u00e9sence de contradictions en hypoth\u00e9se (true=false, Imp...=And...)
     "discriminate"
  - en pr\u00e9sence de H:p&&q=true  "apply andb_true_iff in H"
  - en pr\u00e9sence d'un but p&&q=true "apply andb_true_iff"
  - en pr\u00e9sence d'un but P/\Q  "split"
  - en pr\u00e9sence d'un but P\/Q  "left" ou "right"
  - en pr\u00e9sence d'un but forall x, P x ou P -> Q: "intro" ou "intros"
  - en pr\u00e9sence d'un but t1=t2 o\u00f9 t1 et t2 se r\u00e9duisent en t "reflexivity"
  - enchainer les tactiques, par exemple:
      "destruct c; auto"  tente une preuve auto sur tous les sous-bus g\u00e9n\u00e9r\u00e9s
      "destruct c; try discriminate; auto"   tente aussi discriminate sans \u00e9chouer
  - utiliser une hypoth\u00e8se H: forall x y, P x -> ... -> Q x
    pour prouver Q e: "apply H"  ou "apply H with (y:=...)" 
 *)

Require Import String.
Require Import List.
Include ListNotations.

(* on d\u00e9finit le langage logique *)

Inductive prop :=
  Atom (s:string)
| Imp (p1 p2: prop)
| And (p1 p2: prop)
| Not (p:prop).

(* la comparaison de formules est d\u00e9cidable
  on pourra \u00e9crire: if (prop_dec p1 p2) then ... else ...
*)
Lemma prop_dec: forall (p1 p2: prop), {p1=p2}+{p1<>p2}.
Proof.
  decide equality.
  apply string_dec.
Defined.

(* n\u00e9gation avec simplification pour \u00e9viter Not (Not p) *)
Definition neg p :=
  match p with
    Not p => p
  | p => Not p
  end.

(* repr\u00e9sentation de la formule p&q => q&p *)
Definition exemple := Imp (And(Atom "p") (Atom "q")) (And (Atom "q") (Atom "p")).

(* on manipulera des buts qui sont des couples (liste d'hypoth\u00e8ses, conclusion) *)
Definition goal: Type := list prop * prop.

(* les r\u00e8gles de preuve de la logique des propositions 

       In c h
     --------- pHYP
       h |- c

      h |- p   h |- q           h |- p & q          h |- p & q
     -----------------&_i     --------------&_e1   ------------&_e2
         h |- p & q              h |- p               h |- q

        p::h |- q            In p h   h |- p=>q
      ------------=>_i       -------------------=>_e
        h |- p=>q                 h |- q

          neg q::h |- p       neg q::h |- !p
        ------------------------------------contra
                      h |- q
 *)

Inductive isTrue: list prop -> prop -> Prop :=
  pHYP: forall h c, In c h -> isTrue h c  (* si c est un \u00e9l\u00e9ment de la liste h, isTrue est vrai *)
| pAnd_i: forall h p q, isTrue h p -> isTrue h q -> isTrue h (And p q)
| pAnd_e1: forall h p q, isTrue h (And p q) -> isTrue h p
| pAnd_e2: forall h p q, isTrue h (And p q) -> isTrue h q
| pImp_i: forall h p q, isTrue (p::h) q -> isTrue h (Imp p q)
| pImp_e: forall h p q, In p h -> isTrue h (Imp p q) -> isTrue h q
| pContra: forall h p q, isTrue (neg q::h) p -> isTrue (neg q::h) (Not p) -> isTrue h q.

(* on d\u00e9montre que la formule donn\u00e9e en exemple est prouvable *)
(* TODO 2pts *)

(* 

     -------- pHYP     -------- pHYP
     p&q|-p&q          p&q|-p&q
     -------- pAnd_e2  -------- pAnd_e1
     p&q |- q          p&q |- p
     --------------------------- pAnd_i
             p&q |- q&p
     --------------------------- pImp_i
            |- p&q=>q&p
indications:
On s'inspirera de l'arbre de preuve en appliquant les r\u00e8gles indiqu\u00e9es
==>  apply R ou apply R with (param:=...) si un argument est demand\u00e9
    exemples: apply pHYP.     apply pAnd_e1 with (q:=Atom "q").

     on utilisera simpl auto et/ou tauto pour prouver les In ...
*)
Lemma isTrue_ex: isTrue [] exemple.
Proof.
apply pImp_i.
apply pAnd_i.
- apply pAnd_e2 with (p:= Atom "p").
  apply pHYP.
  simpl; auto.
- apply pAnd_e1 with (q := Atom "q").
  apply pHYP.
  simpl; auto.
Qed.


(* on introduit maintenant le type des arbres de preuve 
   chaque constructeur correspond \u00e0 une r\u00e8gle et contient les
     sous-arbres de preuve et parfois une information, 
     celle demand\u00e9e par apply dans la preuve pr\u00e9c\u00e9dente.
*)
Inductive proof :=
  HYP
| And_i (pr1 pr2: proof)
| And_e1 (q: prop) (pr: proof)
| And_e2 (p: prop) (pr: proof)
| Imp_i (pr: proof)
| Imp_e (p: prop) (pr: proof)
| Contra (p: prop) (pr1 pr2: proof).

Require Import Bool.
Include BoolNotations.

(* renvoie true si pr est un arbre de preuve pour h |- c
   Par exemple, 
   - HYP est bien une preuve si c est dans les hypoth\u00e8ses h
   - And_i pr1 pr2 est bien une preuve de h|-c si c est une conjonction et 
      les pri sont des preuves des arguments de la conjonction
 *)
Check List.In_dec.
Fixpoint check pr h c := 
  match pr,c with
    HYP,  _ => if List.In_dec prop_dec c h then true else false
  | And_i pr1 pr2, And p1 p2 => check pr1 h p1 && check pr2 h p2
  | And_e1 q pr, p => check pr h (And p q)
  | And_e2 p pr, q => check pr h (And p q)
  | Imp_i pr, Imp p q => check pr (p::h) q
  | Imp_e p pr, q => if List.In_dec prop_dec p h then check pr h (Imp p q) else false
  | Contra p pr1 pr2, q => check pr1 (neg q::h) p && check pr2 (neg q::h) (Not p)
  | _,_ => false
  end.

(*
  TODO 3 pts:
  si h |- c est d\u00e9montrable, on peut trouver un arbre de preuve correspondant
  indications:
  preuve par induction sur sur la preuve de isTrue h c (le 1er param\u00e8tre apr\u00e8s h et c)
  - en pr\u00e9sence de H: exists x, P x: "destruct H as [x H]"
  - en pr\u00e9sence de H: P /\ Q: "destruct H as [H1 H2]"
  - en pr\u00e9sence de if cnd then ... else ... : "destruct cnd"
  - pour prouver un exists: "exists ..."
      exemple "exists (And_i ...)" avec les bons param\u00e8tres
      ou "eexists And_i": Coq essaie de deviner les param\u00e8tres
  - en pr\u00e9sence de H:a=b: "rewrite H"
  - "simpl" "auto" "tauto"
*)
Lemma isTrue_check: forall h c, isTrue h c -> exists pr, check pr h c = true.
Proof.
  intros h c; induction 1; simpl; intros; auto.
  - exists HYP.
    simpl.
    destruct (in_dec prop_dec); auto.
  - destruct IHisTrue1 as [pr1 H1].
    destruct IHisTrue2 as [pr2 H2].
    exists (And_i pr1 pr2).
    simpl.
    rewrite H1, H2; auto.
  - destruct IHisTrue as [pr H1].
    exists (And_e1 q pr).
    simpl.
    rewrite H1; auto.
  - destruct IHisTrue as [pr H1].
    exists (And_e2 p pr).
    simpl.
    rewrite H1; auto.
  - destruct IHisTrue as [pr H1].
    exists (Imp_i pr).
    simpl.
    rewrite H1; auto.
  - destruct IHisTrue as [pr H1].
    exists (Imp_e p pr).
    simpl.
    destruct (in_dec prop_dec); auto.
  - destruct IHisTrue1 as [pr1 H1].
    destruct IHisTrue2 as [pr2 H2].
    exists (Contra p pr1 pr2).
    simpl.
    rewrite H1, H2; auto.
  Qed.

(*
  TODO 3 pts: 
  s'il existe un arbre de preuve correct alors le but est prouvable 
indications:
  - en pr\u00e9sence de if cnd then ... else ... : "destruct cnd"
  - en pr\u00e9sence match c with: "destruct c"
  - pour prouver un isTrue, "apply une_r\u00e8gle"
     exemples: "apply pHYP" ou "apply pAnd_e1 with (q:=q)"
  - en pr\u00e9sence de contradictions dans les hypoth\u00e8ses
      (true = false, Imp ... = And ...): "discriminate"
  - en pr\u00e9sence de H: p && q = true: "apply andb_true_iff in H"
  - en pr\u00e9sence de p && q = true: "apply andb_true_iff"
  - en pr\u00e9sence de H: P /\ Q: "destruct H as [H1 H2]"
 *)

Lemma check_isTrue: forall pr h c, check pr h c = true -> isTrue h c.
Proof.
  induction pr; simpl; intros; auto.
  - destruct (in_dec prop_dec) in H; try discriminate.
    apply pHYP; auto.
  - destruct c; try discriminate.
    apply andb_true_iff in H.
    destruct H as [H1 H2].
    apply pAnd_i.
    + apply IHpr1.
      rewrite H1; auto.
    + apply IHpr2.
      rewrite H2; auto.
  - apply pAnd_e1 with (q:=q); auto.
  - apply pAnd_e2 with (p:=p); auto.
  - destruct c; try discriminate.
    apply pImp_i; auto.
  - destruct (in_dec prop_dec); try discriminate.
    apply pImp_e with (p:=p); auto.
  - apply andb_true_iff in H.
    destruct H as [H1 H2].
    apply pContra with (p:=p).
    + apply IHpr1; auto.
    + apply IHpr2; auto.
Qed.

(* exemples d'arbres de preuve *)
Definition prf1 :=
  Imp_i (And_i (And_e2 (Atom "p") HYP)
               (And_e1 (Atom "q") HYP)).

Definition prf2 :=
  Imp_i (And_i
            (And_e1 (Atom "p")
                    (And_i (And_e2 (Atom "p") HYP)
                           (And_e1 (Atom "q") HYP)))
            (And_e1 (Atom "q") HYP)).

(* ce sont des preuves de l'exemple *)
(* TODO 0,5pts *)
Lemma check1: check prf1 [] exemple = true.
Proof.
auto.
Qed.

(* TODO 0,5pts *)
Lemma check2: check prf2 [] exemple = true.
Proof.
auto.
Qed.

(*
  TODO 5pts
  si pr est un arbre de preuve pour h1|- c et h1 inclus dans h2 
  alors pr est un arbre de preuve pour h2 |- c 
  
indications:
  - en pr\u00e9sence de if cnd then ... : "destruct cnd"
  - en pr\u00e9sence de true=false en hypoth\u00e8se : "discriminate"
  - en pr\u00e9sence de H: p&&q=true: "apply andb_true_iff in H"
  - en pr\u00e9sence de H:P/\Q: "destruct H as [H1 H2]"
  - en pr\u00e9sence de H: e1=e2: "rewrite H"
     si demand\u00e9: "rewrite H with (param:=...)"
                 ou "erewrite H"  Coq essaie de deviner le param
  - en pr\u00e9sence de H:forall x ... -> Q x et d'un but Q e: 
      "apply H"
      si demand\u00e9 "apply H with (param:=...)" ou "eapply H"
  - true=false en but: "exfalso"
  - P \/ Q en but: "left" ou "right"
  - en pr\u00e9sence de H: P \/ Q : "destruct H"
  - en pr\u00e9sence de "H: not P": "contradiction H"
  - "simpl" "intros" "auto" "tauto"
*)

Lemma check_mono: forall pr h1 h2 c, (forall p, In p h1 -> In p h2) -> check pr h1 c = true -> check pr h2 c = true.
Proof.
  induction pr; simpl; intros; auto.
  - destruct (in_dec prop_dec); try discriminate.
    destruct (in_dec prop_dec); auto.
  - destruct c; try discriminate.
    apply andb_true_iff in H0.
    destruct H0 as [H1 H2].
    apply andb_true_iff; split.
    + apply IHpr1 with (h1:=h1); auto.
    + apply IHpr2 with (h1:=h1); auto.
  - apply IHpr with (h1:=h1); auto.
  - apply IHpr with (h1:=h1); auto.
  - destruct c; try discriminate.
    apply IHpr with (h1:=c1::h1); auto.
    intros; simpl in *.
    destruct H1; auto.
  - destruct (in_dec prop_dec); try discriminate.
    destruct (in_dec prop_dec); auto.
    apply IHpr with (h1:=h1); auto.
  - apply andb_true_iff in H0.
    destruct H0 as [H1 H2].
    apply andb_true_iff; split.
    + apply IHpr1 with (h1:=(neg c :: h1)); auto.
      intros; simpl in *.
      destruct H0; auto.
    + apply IHpr2 with (h1:=(neg c :: h1)); auto.
      intros; simpl in *.
      destruct H0; auto.
 Qed.


(* TODO 1,5pts
   isTrue est aussi monotone...
indications:
   - preuve directe (sans induction)
   - r\u00e9utiliser (apply) isTrue_check, check_isTrue et check_mono
   - pour appliquer un lemme L de la forme forall x, p x -> q x \u00e0 une hypoth\u00e8se H:p u: "apply L in H"
   - en pr\u00e9sence de H: exists x, P x: "destruct H as [x H]"
   - "apply H with (param:=...)"
 *)

Lemma isTrue_mono: forall h1 c, isTrue h1 c -> forall h2, (forall p, In p h1 -> In p h2) -> isTrue h2 c.
Proof.
intros.
apply isTrue_check in H.
destruct H as [pr Hpr].
apply check_isTrue with (pr:=pr).
apply check_mono with (h1:=h1);auto.
Qed.

(* on s'interesse maintenant \u00e0 la simplification de preuves *)

(* applique la transformation s \u00e0 tous les niveaux *)
Fixpoint apply (s: proof->proof) pr :=
  s (match pr with
    HYP => HYP
  | And_i pr1 pr2 => And_i (apply s pr1) (apply s pr2)
  | And_e1 p pr => And_e1 p (apply s pr)
  | And_e2 p pr => And_e2 p  (apply s pr)
  | Imp_i pr => Imp_i (apply s pr)
  | Imp_e p pr => Imp_e p (apply s pr)
  | Contra p pr1 pr2 => Contra p (apply s pr1) (apply s pr2)
  end).

(* applique une liste de transformations *)
Fixpoint apply_all (l: list (proof->proof)) pr :=
  match l with
    [] => pr
  | s::l => apply_all l (s pr)
  end.

(* une transfo est correcte si elle transforme un arbre de preuve correct en arbre de preuve correct *)
Definition correct (s:proof->proof) := forall pr h c, check pr h c = true -> check (s pr) h c = true.

(* TODO 1pt 
  si toutes les transfos de l sont correctes, apply_all l est correcte
indication:
  - "unfold correct" pour d\u00e9plier sa d\u00e9finition
  - puis preuve par induction sur l
 *)

Lemma apply_all_ok: forall l, (forall s, In s l -> correct s) -> correct (apply_all l).
Proof.
unfold correct.
induction l; auto.
- intros.
  apply IHl.
  + intros.
    apply H; simpl; auto.
  + apply H; simpl; auto.
Qed.

(* non demand\u00e9 *)
Lemma apply_ok: forall s, correct s -> correct (apply s).
Proof.
  unfold correct; intros.
  revert h c H0; induction pr; simpl; intros; auto.
  - destruct c.
    + discriminate.
    + discriminate.
    + apply H.
      simpl.
      apply andb_true_iff in H0.
      destruct H0.
      apply andb_true_iff.
      split.
      ++ apply IHpr1.
         apply H0.
      ++ apply IHpr2.
         apply H1.
    + discriminate.
  - apply H.
    apply IHpr.
    apply H0.
  - apply H.
    simpl.
    apply IHpr.
    apply H0.
  - destruct c.
    + discriminate.
    + apply H.
      simpl.
      apply IHpr.
      apply H0.
    + discriminate.
    + discriminate.
  - apply H.
    simpl.
    destruct in_dec.
    + apply IHpr.
      apply H0.
    + auto.
  - apply H.
    simpl.
    apply andb_true_iff in H0.
    destruct H0.
    apply andb_true_iff.
    split.
    + apply IHpr1.
      apply H0.
    + apply IHpr2.
      apply H1.
Qed.


(* quelques simplifications basiques *)
Definition simpl_And_e1 pr :=
  match pr with
    And_e1 _ (And_i pr1 pr2) => pr1
  | _ => pr
  end.

Definition simpl_And_e2 pr :=
  match pr with
  | And_e2 _ (And_i pr1 pr2) => pr2
  | _ => pr
  end.

Definition simpl_Imp_e pr :=
  match pr with
  | Imp_e _ (Imp_i pr) => pr
  | _ => pr
  end.

(* TODO 1,5pts
indications
  - en pr\u00e9sence de correct: "unfold"
  - preuve par cas sur pr: "destruct"
  - en pr\u00e9sence de H:p&&q=true "apply andb_prop in H"
  - "simpl" "auto" "tauto" "intros" ...
 *)

Lemma simpl_And_e1_ok: correct simpl_And_e1.
Proof.
unfold correct.
destruct pr; auto.
intros.
destruct pr; auto.
simpl in *.
apply andb_true_iff in H.
destruct H as [H1 H2]; auto.
Qed.

(* TODO 1,5pts
indications
  - en pr\u00e9sence de correct: "unfold"
  - preuve par cas sur pr: "destruct"
  - en pr\u00e9sence de H:p&&q=true "apply andb_prop_iff in H"
  - "simpl" "auto" "tauto" "intros" ...
*)
Lemma simpl_And_e2_ok: correct simpl_And_e2.
Proof.
unfold correct.
destruct pr; auto.
intros.
destruct pr; auto.
simpl in *.
apply andb_true_iff in H.
destruct H as [H1 H2]; auto.
Qed.
