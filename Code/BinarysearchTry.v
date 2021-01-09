From Equations Require Import Equations.
Require Import Arith.
Require Import Lia.
Require Import Coq.Lists.SetoidList. (* For Sorted *)
Require Import Sumbool.
Require Export JMeq.
Import Sigma_Notations.
Require Import Coq.Program.Tactics.

Notation dec x := (sumbool_of_bool x).
  

Lemma lte_div2 : 
forall (n m : nat),
    n <= m
  ->
    Nat.div2 n <= Nat.div2 m.
    
intros.
rewrite Nat.div2_div.
rewrite Nat.div2_div.
apply Nat.div_le_mono.
lia.
apply H.
Qed.


Lemma lte_plus_div2 : 
forall (n m : nat),
    m <= (n + m) / 2
  -> 
    m <= n.
    
intros.
apply mult_le_compat_l with (p:= 2) in H.
apply Nat.le_trans with (p:= 2*(n+m)/2) in H.
replace (2*(n+m)) with ((n+m)*2) in H.
rewrite Nat.div_mul with (b:= 2) in H.
lia.
lia.
lia.
apply Nat.div_mul_le.
lia.
Qed.


Lemma lt_div2_min : 
forall (n m : nat),
    n < m
  ->
    Nat.div2 (n + m) - n < m - n.

intros.
destruct (Nat.div2 (n+m)<? m) as []eqn:?.
apply Nat.ltb_lt in Heqb.
lia.
apply Nat.ltb_ge in Heqb.
rewrite Nat.div2_div in Heqb.
apply lte_plus_div2 in Heqb.
apply le_not_lt in Heqb.
contradiction.
Qed.


Set Program Mode.


Equations? binarysearch (l: list nat) (target L R :nat) : option nat by wf (R-L) lt:=
binarysearch l t L R with dec(R <=? L) =>
  | left H => None;
  | right H with dec(t =? nth (Nat.div2 L+R) l (t+1))=> 
      | left H => Some (Nat.div2 L+R);
      | right H => if nth ((Nat.div2 L+R)) l (t+1) <? t 
                     then binarysearch l t ((Nat.div2 (L+R))+1) R
                     else binarysearch l t L (Nat.div2 (L+R)).  
                     
                     
apply leb_complete_conv in H.
apply Nat.le_lt_trans with (m:= R - (Nat.div2 (2*L) + 1)).
rewrite Nat.sub_add_distr.
rewrite Nat.sub_add_distr.
apply Nat.sub_le_mono_r.
apply Nat.sub_le_mono_l.
apply lte_div2.
lia.
rewrite Nat.div2_double.
rewrite Nat.sub_add_distr.
apply Nat.sub_gt in H.
lia.
apply leb_complete_conv in H.
apply lt_div2_min.
apply H.
Defined.

Check binarysearch_elim.

(* The return type containing the correctness property: *)
(* {p: option nat | Sorted le l -> (forall (e:nat), p=Some e -> nth e l (target+1) = target) /\ (p=None -> ~ In target l)}. *)
 
(* This is one part of the correctness property: *)
Theorem binarysearch_correct : forall (l : list nat) (a index : nat),
Sorted le l
->
~ In a l
-> 
binarysearch l a 0 (length l) = None.

intros.
apply binarysearch_elim.
intros.
trivial.
intros.
inversion e.
apply beq_nat_true in H2.
Admitted.
(* 2:{
intros.
destruct (nth (Nat.div2 L + R) l0 0 <? target) as []eqn:?.
apply H1.
apply H2. *)

