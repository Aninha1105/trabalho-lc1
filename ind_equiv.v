Require Import Arith Lia.
Definition PIM :=
forall P: nat -> Prop, 
(P 0) ->
(forall k, P k -> P (S k)) ->
forall n, P n.

Definition PIF :=
forall Q: nat -> Prop, 
(forall k, (forall m, m<k -> Q m) -> Q k) ->
forall n, Q n.

Lemma PIF_to_PIM: PIF -> PIM.
Proof.
  intros h P hbase hsucc.--
  apply (h P).
  intros n hm.
  destruct n.
  - assumption.
  - assert (hn : P n).
    {
      apply hm.
      exact (Nat.lt_succ_diag_r _).
    }
  exact (hsucc n hn).
Qed.

Lemma PIM_to_PIF: PIM -> PIF.
Proof.
  intros hweak P h.
  specialize (hweak (fun n => forall m, m < n -> P m)).
  assert (hbase : (fun n : nat => forall m : nat, m < n -> P m) 0).
  { intros m hm. inversion hm. }
  assert (hsucc:((forall n : nat,
         (fun n0 : nat => forall m : nat, m < n0 -> P m) n ->
         (fun n0 : nat => forall m : nat, m < n0 -> P m) (S n)))).
  {
    intros n hm m hnm.
    assert (hm2 : m = n \/ m < n). lia.
    destruct hm2.
    - subst m. apply h. assumption.
    - apply hm. assumption.
  }

  simpl in hweak.
  specialize (hweak hbase hsucc).
  intro n.
  exact (hweak (S n) n (Nat.lt_succ_diag_r _)).
Qed.



Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  constructor.
  - exact PIM_to_PIF.
  - exact PIF_to_PIM.
Qed.