From Equations Require Import Equations.
Require Import Arith.
Require Import Lia.
Require Import Coq.Lists.SetoidList. (* For Sorted *)
Require Import Coq.Sorting.Permutation. (* For Permutation *)


Definition filter_lte (a: nat) (l : list nat) := filter (fun n=> n <=? a) l.
Definition filter_gt (a: nat) (l : list nat) := filter (fun n=> negb(n <=? a)) l.


Lemma lte_nil : forall (n : nat), filter_lte n nil = nil.

intros.
trivial.
Qed.


Lemma gt_nil : forall (n : nat), filter_gt n nil = nil.

intros.
trivial.
Qed.


Equations? quicksort (l : list nat) : list nat by wf (length l) lt:=
quicksort nil := nil ;
quicksort (h :: t) := (quicksort (filter_lte h t)) ++ (h :: (quicksort (filter_gt h t))).

apply Nat.le_lt_trans with (m := (length t)).
unfold filter_lte.
induction t.
reflexivity.
simpl.
destruct (a <=? h) as []eqn:?.
simpl.
destruct IHt.
intuition.
trivial.
intuition.
rewrite -> IHt.
lia.
auto.
lia.
apply Nat.le_lt_trans with (m := (length t)).
unfold filter_gt.
induction t.
reflexivity.
simpl.
destruct (a <=? h) as []eqn:?.
simpl.
destruct IHt.
intuition.
intuition.
intuition.
simpl.
destruct IHt.
intuition.
intuition.
intuition.
intuition.
Defined.

Transparent quicksort.

Check quicksort_elim. 

(* -------------------------------------------------------------------------------
    PERMUTATION 
------------------------------------------------------------------------------- *)

Lemma perm_app : forall (l l1 l2 : list nat), 
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


Lemma perm_lte_gt : 
forall (l : list nat) (n : nat), 
  Permutation l (filter_lte n l ++ filter_gt n l).

intros.
induction l.
simpl.
apply perm_nil.
destruct (a <=? n) as []eqn:?.
unfold filter_lte.
unfold filter.
rewrite -> Heqb.
unfold filter_gt.
unfold filter.
rewrite -> Heqb.
simpl.
apply perm_skip.
apply IHl.
unfold filter_lte.
unfold filter.
rewrite -> Heqb.
unfold filter_gt.
unfold filter.
rewrite -> Heqb.
simpl.
apply Permutation_cons_app.
apply IHl.
Qed.


Theorem quicksort_permutation : 
forall (l : list nat), 
  Permutation l (quicksort l).

intros.
apply quicksort_elim.
apply perm_nil.
intros.
apply perm_app.
exists (filter_lte n l0).
exists (n::filter_gt n l0).
split.
apply H.
split.
apply perm_skip.
apply H0.
apply Permutation_cons_app.
apply perm_lte_gt.
Qed.

(* -------------------------------------------------------------------------------
    SORTED
------------------------------------------------------------------------------- *)

Lemma in_lte : 
forall (elem n : nat), 
    (exists (l : list nat), In elem (filter_lte n l)) 
  -> 
    elem <= n.

intros.
elim H.
intros.
unfold filter_lte in H0.
apply filter_In in H0.
intuition.
apply leb_complete.
apply H2.
Qed.


Lemma in_gt : 
forall (elem n : nat), 
    (exists (l : list nat), In elem (filter_gt n l)) 
  -> 
    elem > n.
    
intros.
elim H.
intros.
unfold filter_gt in H0.
apply filter_In in H0.
intuition.
apply leb_complete_conv.
apply Bool.negb_true_iff.
apply H2.
Qed.


Lemma in_qs : 
forall (l : list nat) (elem : nat), 
    In elem l 
  <->
    In elem (quicksort l).
    
intros.
split.
apply Permutation_in.
apply quicksort_permutation.
apply Permutation_in.
apply Permutation_sym.
apply quicksort_permutation.
Qed.


Lemma sort_app : 
forall (l l': list nat) (n : nat), 
    Sorted le l 
  -> 
      Sorted le l' 
    -> 
        (forall (elem : nat), In elem l -> elem <= n)
      -> 
          (forall (elem : nat), In elem l' -> elem > n)
        -> 
          Sorted le (app l (n::l')).

intros.
induction l.
simpl.
apply Sorted_cons.
apply H0.
apply In_InfA.
intros.
apply Nat.lt_le_incl.
apply H2.
apply H3.
rewrite <- app_comm_cons.
apply Sorted_cons.
apply IHl.
apply Sorted_inv in H.
apply H.
intros.
apply H1.
apply in_cons.
apply H3.
apply Sorted_inv in H.
destruct H.
apply InfA_app.
apply H3.
apply HdRel_cons.
apply H1.
apply in_eq.
Qed.


Theorem quicksort_sorted : 
forall (l : list nat), 
  Sorted le (quicksort l).

intros.
apply quicksort_elim.
trivial.
intros.
apply sort_app.
apply H.
apply H0.
intros.
apply in_lte.
exists l0.
apply in_qs.
apply H1.
intros.
apply in_gt.
exists l0.
apply in_qs.
apply H1.
Qed.


(* -------------------------------------------------------------------------------
    CORRECTNESS
------------------------------------------------------------------------------- *)

Theorem quicksort_correct : 
forall (l : list nat), 
  Sorted le (quicksort l) /\ Permutation l (quicksort l).
  
intros.
split.
apply quicksort_sorted.
apply quicksort_permutation.
Qed.
