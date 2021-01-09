From Equations Require Import Equations.
Require Import Arith.
Require Import Lia.
Require Import Coq.Lists.SetoidList. (* For Sorted *)
Require Import Coq.Sorting.Permutation. (* For Permutation *)


Equations? merge (l l' : list nat) : list nat by wf (length l + length l'):=
merge xs nil := xs ;
merge nil ys := ys ;
merge (x::xs) (y::ys) := if x <=? y then x :: merge xs (y::ys) else y :: merge (x::xs) ys.

lia.
Qed.


Transparent merge.
Check merge_elim.


Lemma merge_nil : 
forall (l : list nat), 
  merge nil l = l.
  
intros.
induction l.
now simp merge.
apply merge_equation_2.
Qed.


Definition first_half (l: list nat) := (firstn (Nat.div2 (length l)) l).
Definition second_half (l: list nat) := (skipn (Nat.div2 (length l)) l).


Equations? mergesort (l : list nat) : list nat by wf (length l) lt :=
mergesort nil := nil;
mergesort (a::nil) := a::nil;
mergesort l := merge (mergesort (first_half l)) (mergesort (second_half l)).

apply lt_n_S.
induction (length l0).
auto.
apply Nat.le_lt_trans with (m := (Nat.div2 (S n1))).
apply firstn_le_length.
apply Nat.le_lt_trans with (m := S n1).
apply Nat.div2_decr.
auto.
auto.
replace l with (n :: n0 :: l0).
unfold second_half.
induction (l0).
simpl.
auto.
apply Nat.le_lt_trans with (m := (length ((n :: n0 :: a :: l1)))-((Nat.div2 (length (n :: n0 :: a :: l1))))).
apply Nat.eq_le_incl.
apply skipn_length.
replace (S (S (length (a :: l1)))) with (length (n :: n0 :: a :: l1) ).
apply Nat.sub_lt.
intuition.
apply Nat.lt_le_incl.
apply Nat.lt_div2.
simpl.
apply Nat.lt_0_succ.
simpl.
apply Nat.lt_0_succ.
intuition.
intuition.
Defined.

Transparent mergesort.
Check mergesort_elim.

(* -------------------------------------------------------------------------------
    PERMUTATION 
------------------------------------------------------------------------------- *)

Lemma perm_merge : 
forall (l1 l2 l3 : list nat),
    Permutation l1 (app l2 l3)
  ->
    Permutation l1 (merge l2 l3).

intros.
apply Permutation_trans with (l' := l2++l3).
apply H.
apply merge_elim.
intros.
rewrite -> app_nil_r.
intuition.
intros.
rewrite -> app_nil_l.
intuition.
intros.
destruct (n0 <=? n) as []eqn:?.
simpl.
apply perm_skip.
apply H0.
simpl.
apply Permutation_trans with (l' := n :: (n0 :: l) ++ l0).
apply Permutation_sym.
apply Permutation_middle.
simpl.
apply perm_skip.
apply H1.
Qed.


Lemma perm_app : 
forall (l l1 l2 : list nat), 
    (exists (l3 l4 : list nat),
      Permutation l3 l1 /\ Permutation l4 l2 /\ Permutation l (l3 ++ l4))
  -> 
    Permutation l (l1 ++ l2).
    
intros.
elim H.
intros.
elim H0.
intros.
apply Permutation_trans with (l' := (x ++ x0)).
intuition.
apply Permutation_app.
intuition.
intuition.
Qed.


Theorem mergesort_permutation : 
forall (l : list nat), 
  Permutation l (mergesort l).
  
intros.
apply mergesort_elim.
apply perm_nil.
intros.
apply Permutation_refl.
intros.
apply perm_merge.
apply perm_app.
exists (firstn (Nat.div2 (length (n :: n0 :: l0))) (n :: n0 :: l0)).
exists (skipn (Nat.div2 (length (n :: n0 :: l0))) (n :: n0 :: l0)).
split.
apply H.
split.
apply H0.
replace (firstn (Nat.div2 (length (n :: n0 :: l0))) (n :: n0 :: l0) ++
   skipn (Nat.div2 (length (n :: n0 :: l0))) (n :: n0 :: l0)) with (n :: n0 :: l0).
intuition.
rewrite -> firstn_skipn with (n :=(Nat.div2 (length (n :: n0 :: l0)))).
trivial.
Qed.

(* -------------------------------------------------------------------------------
    SORTED
------------------------------------------------------------------------------- *)

Lemma hdrel_merge : 
forall (l l' : list nat) (a a' : nat), 
    Sorted le (a :: l)
  ->
      Sorted le (a' :: l')
    ->
        a <= a'
      -> 
        HdRel le a (merge l (a' :: l')) /\ HdRel le a (merge (a' :: l') l).
        
intros.
destruct l.
simp merge.
intuition.
split.
destruct (n <=? a') as []eqn:?.
simp merge.
rewrite Heqb.
apply HdRel_cons.
apply Sorted_inv in H .
intuition.
apply HdRel_inv in H3.
intuition.
simp merge.
rewrite Heqb.
apply HdRel_cons.
intuition.
destruct (a' <=? n) as []eqn:?.
simp merge.
rewrite Heqb.
apply HdRel_cons.
intuition.
simp merge.
rewrite Heqb.
apply HdRel_cons.
apply Sorted_inv in H.
intuition.
apply HdRel_inv in H3.
intuition.
Qed.


Lemma merge_sorts : 
forall (l : list nat),
    Sorted le l
  ->
    forall (l' : list nat),
        Sorted le l'
      ->
        Sorted le (merge l l').
        

induction 1.
intros.
rewrite -> merge_nil.
apply H.
induction 1.
simp merge.
apply Sorted_cons.
apply H.
apply H0.
destruct (a <=? a0) as []eqn:?.
simp merge.
rewrite -> Heqb.
apply Sorted_cons.
apply IHSorted.
apply Sorted_cons.
apply H1.
apply H2.
apply hdrel_merge.
constructor.
apply H.
apply H0.
constructor.
apply H1.
apply H2.
apply leb_complete.
apply Heqb.
simp merge.
rewrite -> Heqb.
apply Sorted_cons.
apply IHSorted0.
apply hdrel_merge.
constructor.
apply H1.
apply H2.
constructor.
apply H.
apply H0.
apply leb_complete.
intuition.
apply leb_correct.
apply Nat.leb_nle in Heqb.
apply Nat.lt_le_incl.
apply not_ge.
auto.
Qed.


Theorem mergesort_sorted : 
forall (l : list nat), 
  Sorted le (mergesort l).
  
intros.
apply mergesort_elim.
trivial.
intros.
apply Sorted_cons.
trivial.
trivial.
intros.
apply merge_sorts.
apply H.
apply H0.
Qed.

(* -------------------------------------------------------------------------------
    CORRECTNESS
------------------------------------------------------------------------------- *)


Theorem mergesort_correct : 
forall (l : list nat), 
  Sorted le (mergesort l) /\ Permutation l (mergesort l).
intros.
split.
apply mergesort_sorted.
apply mergesort_permutation.
Qed.

Check mergesort_elim.
Print mergesort_elim.

