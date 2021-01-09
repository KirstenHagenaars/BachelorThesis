From Equations Require Import Equations.
Require Import Arith.
Require Import Lia.
Require Import Coq.Lists.SetoidList. (* For Sorted *)
Require Import Coq.Sorting.Permutation. (* For Permutation *)
Require Import Sumbool.
Import Sigma_Notations.
Require Export JMeq.
Require Import Coq.Program.Tactics.
Require Import Vectors.VectorDef.

Arguments Vector.nil {A}.
Arguments Vector.cons {A} a {n} v : rename.

Notation vector := Vector.t.
Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.
Notation dec x := (sumbool_of_bool x).


Set Program Mode.


Equations app {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  app Vnil w := w ;
  app (Vcons a v) w := Vcons a (app v w).
  

Inductive filtered (f:nat->bool) : forall {n}, (vector nat n) -> Prop :=
| filtered_nil : filtered f Vnil
| filtered_cons {h n} {v:vector nat n}: f h = true -> filtered f v -> filtered f (Vcons h v).


Equations len_filtered {n} (v:vector nat n)(f:nat->bool) : nat:=
len_filtered Vnil f := 0;
len_filtered (Vcons h t) f := match dec(f h) with
   | left p0 => 1+len_filtered t f
   | right q0 => len_filtered t f
           end.

Transparent len_filtered.


Equations? filter {n} (v:vector nat n)(f:nat->bool) : 
  Σ (p : nat), {w:vector nat p|p = len_filtered v f /\ p<=n /\ filtered f w}:=
filter Vnil f := (0, Vnil);
filter (Vcons h t) f with dec(f h) :=
   { | left p0 => (_, Vcons h ((filter t f).2)) ;
     | right q0 => (_, (filter t f).2)}.
     
intuition.
apply filtered_nil.
destruct filter as [a [b [d e]]]. 
simpl. 
intuition.
constructor.
intuition.
intuition.
split.
destruct filter as [a [b c]]. 
intuition.
destruct filter as [a [b c]]. 
simpl. 
intuition.
Defined.


Transparent filter.

Definition filter_lte {n} (a: nat) (v:vector nat n) := filter v (fun x => x <=? a).
Definition filter_gt {n} (a: nat) (v:vector nat n) := filter v (fun x=> negb(x <=? a)).


Lemma len_fixed {l}: 
forall (t: vector nat l) (h:nat),
  len_filtered t (fun x : nat => x <=? h) + len_filtered t (fun x : nat => negb (x <=? h)) = l.

intros.
induction t.
intuition.
destruct (dec (h0 <=? h)) as []eqn:?.
simp len_filtered.
rewrite Heqs. simpl.
rewrite e. simpl.
rewrite IHt.
trivial.
simp len_filtered.
rewrite Heqs. simpl.
rewrite e. simpl.
rewrite Nat.add_succ_r.
rewrite IHt.
trivial.
Qed.


Equations? quicksort {n} (l : vector nat n) : vector nat n by wf n lt :=
    quicksort Vnil := Vnil ;
    quicksort (Vcons h t):= app (quicksort (filter_lte h t).2) (Vcons h (quicksort (filter_gt h t).2)).
    
destruct filter_lte as [a [b [c d]]]. simpl. intuition.
destruct filter_gt as [a [b [c d]]]. simpl. intuition.
destruct filter_lte with (a:=h)(v:= t)as [a [b [c d]]]. 
destruct filter_gt with (a0:=h)(v:= t) as [e [f [g i]]].
simpl.
rewrite c. rewrite g.
rewrite Nat.add_succ_r.
apply eq_S.
apply len_fixed.
Defined.

Check quicksort_elim.


Equations In {A n} (x : A) (v : vector A n) : Prop :=
  In x Vnil := False;
  In x (Vcons a v) := (x = a) \/ In x v.


(* From Sozeau *)
Inductive All {A : Type} (P : A -> Prop) : forall {n}, vector A n -> Prop :=
| All_nil : All P Vnil
| All_cons {a n} {v : vector A n} : P a -> All P v -> All P (Vcons a v).


(* From Sozeau *)
Lemma All_impl {A : Type} (P Q : A -> Prop) {n} (v : vector A n) : 
(forall x, P x -> Q x) -> All P v -> All Q v.

Proof. 
induction 2; 
constructor; 
auto. 
Qed.

Derive Signature for All.


(* From Sozeau *)
Lemma In_All {A P n} (v : vector A n) : 
    All P v 
  <-> 
    (forall x, In x v -> P x).
    
Proof.
split. 
induction 1. 
intros. 
depelim H. 
auto. 
intros x; simpl. 
simp In. 
intuition. 
subst; auto.
induction v; simpl; intros; auto; constructor. 
apply H; simp In; auto.
firstorder.
Qed.


Lemma In_app {A n m} : 
forall (x: A) (v : vector A n) (w : vector A m),
    In x (app v w)
  -> 
    In x v \/ In x w.
    
intros a l b.
elim l; simpl; auto.
intros.
elim H0; auto.
intro H1.
simp In. 
intuition.
intuition.
simp In.
intuition.
Qed.


(* From Sozeau, except for the proof *)
Lemma All_app {A P n m} (v : vector A n) (w : vector A m) :
    All P v 
  -> 
      All P w 
    -> 
      All P (app v w).
      
Proof.
intros.
rewrite In_All.
intros.
rewrite In_All in H.
rewrite In_All in H0.
apply In_app in H1.
destruct H1.
apply H.
apply H1.
apply H0.
apply H1.
Qed.


(* From Sozeau *)
Inductive Sorted {A : Type} (R : A -> A -> Prop) : forall {n}, vector A n -> Prop :=
| Sorted_nil : Sorted R Vnil
| Sorted_cons {a n} {v : vector A n} : All (R a) v -> Sorted R v -> Sorted R (Vcons a v).
Import Sigma_Notations.

Derive Signature for Sorted.

Definition sorted {n } (v : vector nat n) := Sorted (fun x y => x <= y) v.


Lemma sorted_inv {n}: 
forall (a : nat) (v:vector nat n),
    sorted (Vcons a v) 
  -> 
    sorted v /\ All ((fun x y => x <= y)a) v.
    
intros.
inversion H.
replace v with v0.
auto.
apply Eqdep.EqdepTheory.inj_pair2 with (P:= (fun n : nat => vector nat n)) (p := n).
apply H2.
Qed.


Lemma filtered_All {n} : 
forall (x : nat) (R : nat -> bool) (v:vector nat n),
    filtered (fun x : nat => R x ) v
  ->
      In x v 
    ->
      R x = true.
      
intros.
induction H.
contradiction.
simp In in H0.
elim H0.
intros.
rewrite H2.
intuition.
apply IHfiltered.
Qed.


(* -------------------------------------------------------------------------------
    PERMUTATION 
------------------------------------------------------------------------------- *)

Print Permutation.

Inductive VPermutation {A}: forall {n m}, (vector A n) -> (vector A m) -> Prop :=
    Vperm_nil : VPermutation Vnil Vnil
  | Vperm_skip {x n m} {v:vector A n} {w:vector A m}:
                VPermutation v w -> VPermutation (Vcons x v) (Vcons x w)
  | Vperm_swap {x y n} {v:vector A n} : VPermutation (Vcons y (Vcons x v)) (Vcons x (Vcons y v))
  | Vperm_trans {n m o} {u:vector A n} {v:vector A m} {w:vector A o}: 
                 VPermutation u v -> VPermutation v w -> VPermutation u w.
                 
                 
                 
Transparent In.

Lemma VPermutation_in {n m}: 
forall  (w: vector nat m) (v: vector nat n) (a : nat), 
    VPermutation v w
  ->
      In a v
    -> 
      In a w.
      
intros w v a H.
induction H.
tauto.
simpl.
tauto.
simpl.
tauto.
tauto.
Qed.


Lemma VPermutation_refl {A n} : 
forall (v:vector A n), 
  VPermutation v v.
  
Proof.
induction v; constructor.
intuition.
Qed.


Lemma VPermutation_trans {A n m o}: 
forall (u:vector A n) (v:vector A m) (w:vector A o),
    VPermutation u v 
  -> 
      VPermutation v w 
    -> 
      VPermutation u w.
      
Proof.
intros u v w.
exact Vperm_trans.
Qed.


Lemma VPermutation_sym {n m}: 
forall  (v: vector nat m) (w: vector nat n),
    VPermutation v w
  ->
    VPermutation w v.
    
intros l l' Hperm; induction Hperm; auto.
constructor.
apply Vperm_skip.
intuition.
apply Vperm_swap.
apply VPermutation_trans with (v0:= v).
intuition.
intuition.
Qed.


Lemma V_app_comm_cons {n m}: 
forall  (v: vector nat m) (w: vector nat n) (a : nat), 
  Vcons a (app v w) = app (Vcons a v) w.
  
intros.
simp app.
trivial.
Qed.


Lemma VPermutation_app_tail {A n m o} : 
forall (v:vector A n) (v1:vector A m) (v2:vector A o),
    VPermutation v1 v2 
  -> 
    VPermutation (app v1 v) (app v2 v).
    
Proof.
intros.
induction H as [|x l l'|x y l|l l' l'']. 
simp app.
intuition.
apply VPermutation_refl.
simp app.
apply Vperm_skip.
intuition.
simp app.
apply Vperm_swap.
apply VPermutation_trans with (v1:= app v0 v).
intuition.
intuition.
Qed.


Lemma VPermutation_app_head {A n m o} : 
forall (v:vector A n) (v1:vector A m) (v2:vector A o),
    VPermutation v1 v2 
  -> 
    VPermutation (app v v1) (app v v2).
    
Proof.
intros.
induction v.
simp app.
simp app.
apply Vperm_skip.
intuition.
Qed.


Lemma VPermutation_app {A n m o p}: 
forall (u:vector A n) (v:vector A m) (w:vector A o) (x: vector A p),
    VPermutation u w 
  -> 
      VPermutation v x 
    -> 
      VPermutation (app u v) (app w x).
      
Proof.
intros.
induction H as [|a u w|a y u|u q l'']; 
repeat rewrite <- app_comm_cons; auto.
simp app.
apply Vperm_skip.
intuition.
simp app.
apply VPermutation_trans with (v1 :=Vcons y (Vcons a (app v0 x))).
apply Vperm_skip.
apply Vperm_skip.
apply VPermutation_app_head.
apply H0.
apply Vperm_swap.
apply VPermutation_trans with (v1 := app v0 v).
apply VPermutation_app_tail.
intuition. 
intuition. 
Qed.


Lemma perm_app {m n o p q}: 
forall (v: vector nat m) (v1: vector nat n) (v2: vector nat o)
(v3: vector nat p) (v4: vector nat q),
    VPermutation v3 v1
  -> 
      VPermutation v4 v2
    -> 
        VPermutation v (app v3 v4)
      -> 
        VPermutation v (app v1 v2).
        
intros.
apply VPermutation_trans with (v0 := (app v3 v4)).
intuition.
apply VPermutation_app.
intuition.
intuition.
Qed.


Lemma VPermutation_middle {A n m }: 
forall (v1: vector A n) (v2: vector A m) (a : A),
  VPermutation (Vcons a (app v1 v2)) (app v1 (Vcons a v2)).
  
induction v1.
intros.
simp app.
apply VPermutation_refl.
intros.
simp app.
apply VPermutation_trans with (v:= (Vcons h (Vcons a (app v1 v2)))).
apply Vperm_swap.
apply Vperm_skip.
apply IHv1.
Qed.


Lemma VPermutation_cons_app {A n m o}: 
forall (v: vector A n) (v2: vector A m) (v1: vector A o) (a : A),
    VPermutation v (app v1 v2) 
  -> 
    VPermutation (Vcons a v) (app v1 (Vcons a v2)).
    
intros.
apply VPermutation_trans with (v0 := Vcons a (app v1 v2)).
apply Vperm_skip.
intuition.
apply VPermutation_middle.
Qed.


Lemma perm_lte_gt {n} : 
forall (v: vector nat n) (a : nat), 
  VPermutation v (app (filter_lte a v).2 (filter_gt a v).2).
  
intros.
induction v.
simpl.
simp app.
apply Vperm_nil.
apply VPermutation_trans 
with (v0:= Vcons h ((app (proj1_sig (filter_lte a v).2) (proj1_sig (filter_gt a v).2)))).
apply Vperm_skip.
apply IHv.
unfold filter_lte.
unfold filter_gt.
simpl.
destruct (dec (h <=? a)) as []eqn:?.
destruct (dec (negb (h <=? a))) as []eqn:?.
inversion e.
inversion e0.
rewrite H0 in H1.
discriminate.
simpl.
simp app.
apply Vperm_skip.
apply VPermutation_refl.
destruct (dec (negb (h <=? a))) as []eqn:?.
simpl.
apply VPermutation_cons_app.
apply VPermutation_refl.
inversion e.
inversion e0.
rewrite Bool.negb_false_iff in H1.
rewrite H0 in H1.
discriminate.
Qed.


Theorem quicksort_permutation {n}: 
forall (v : vector nat n), 
  VPermutation v (quicksort v).
  
intros.
apply quicksort_elim.
apply Vperm_nil.
intros.
destruct (quicksort_obligation_3 n0 h t0).
simpl.
apply perm_app with (v3:= (proj1_sig (filter_lte h t0).2)) (v4:= Vcons h (proj1_sig (filter_gt h t0).2)).
apply H.
apply Vperm_skip.
apply H0.
apply VPermutation_cons_app.
apply perm_lte_gt.
Qed.

(* -------------------------------------------------------------------------------
    SORTED
------------------------------------------------------------------------------- *)

Lemma in_lte {n} : 
forall (h x: nat) (t: vector nat n),
    In x (proj1_sig (filter_lte h t).2)
  ->
    x <= h.
    
intros.
destruct filter_lte as [a [b [c d]]]. 
simpl in H.
intuition.
apply leb_complete.
apply filtered_All with (v:= b) (R:= (fun x : nat => x <=? h)).
intuition.
apply H.
Qed.


Lemma in_gt {n} : 
forall (h x : nat) (t: vector nat n),
    In x (proj1_sig (filter_gt h t).2)
  ->
    x > h.
    
intros.
destruct filter_gt as [a [b [c d]]]. 
simpl in H.
apply leb_complete_conv. 
rewrite <- Bool.negb_true_iff.
apply filtered_All with (v:= b) (R:= (fun x : nat => negb (x <=? h))).
intuition.
apply H.
Qed.


Lemma in_qs {n} : 
forall (t: vector nat n) (elem : nat), 
    In elem t 
  <->
    In elem (quicksort t).
    
intros.
split.
intros.
apply VPermutation_in with (v:= t).
apply quicksort_permutation.
apply H.
apply VPermutation_in.
apply VPermutation_sym.
apply quicksort_permutation.
Qed.


Lemma sort_app {l l'}: 
forall (v : vector nat l) (v': vector nat l') (n : nat), 
    sorted v
  -> 
      sorted v' 
    -> 
        All (fun y : nat => y > n) v'
      -> 
          All (fun y : nat => y <= n) v
        -> 
          sorted (app v (Vcons n v')).
          
intros.
induction v.
simp app.
apply Sorted_cons.
apply All_impl with (P:=  (fun y : nat => y > n)).
intros.
intuition.
apply H1.
apply H0.
simp app.
apply Sorted_cons.
apply All_app.
apply sorted_inv in H.
intuition.
constructor.
rewrite In_All in H2.
apply H2.
constructor.
trivial.
apply In_All.
intros.
apply Nat.le_trans with (m:= n).
rewrite In_All in H2.
apply H2.
constructor.
trivial.
rewrite In_All in H1.
apply Nat.lt_le_incl.
apply H1.
apply H3.
apply IHv.
apply sorted_inv in H.
intuition.
apply In_All.
intros.
rewrite In_All in H2.
apply H2.
simp In.
intuition.
Qed.


Theorem quicksort_sorted {n} : 
forall (v : vector nat n), 
  sorted (quicksort v).
  
intros.
apply quicksort_elim.
constructor.
intros.
destruct (quicksort_obligation_3 n0 h t0).
simpl.
apply sort_app.
apply H.
apply H0.

apply In_All.
intros.
rewrite <- in_qs in H1.
apply in_gt with (t := t0).
apply H1.

apply In_All.
intros.
rewrite <- in_qs in H1.
apply in_lte with (t := t0).
apply H1.
Qed.


(* -------------------------------------------------------------------------------
    CORRECTNESS
------------------------------------------------------------------------------- *)

Theorem quicksort_correct {n} : 
forall (v : vector nat n), 
  sorted (quicksort v) /\ VPermutation v (quicksort v).
  
intros.
split.
apply quicksort_sorted.
apply quicksort_permutation.
Qed.

