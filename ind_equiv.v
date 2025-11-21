(** * Equivalência entre o Princípio da Indução Matemática e o Princípio da Indução Forte *)

Require Import Arith Lia.

(** Seja [P] uma propriedade sobre os números naturais. O Princípio da *)
(** Indução Matemática (PIM) pode ser enunciado da seguinte forma:  
    1. Base: P vale para 0.
    2. Passo: Se P vale para k, então vale para k+1. *)

Definition PIM :=
forall P: nat -> Prop, 
(P 0) ->
(forall k, P k -> P (S k)) ->
forall n, P n.

(** Seja [Q] uma propriedade sobre os números naturais. O Princípio da *)
(** Indução Forte (PIF) pode ser enunciado da seguinte forma:  
    1. Passo Forte: Se Q vale para TODOS os antecessores de k, vale para k. *)

Definition PIF :=
forall Q: nat -> Prop, 
(forall k, (forall m, m<k -> Q m) -> Q k) ->
forall n, Q n.

(** Prove que estes princípios são equivalentes: *)

(** -----------------------------------------------------------------
    LEMA 1: Indução Forte implica Indução Matemática 
    -----------------------------------------------------------------
    Estratégia: Assumimos que o PIF é válido e tentamos provar o PIM.
    Mostramos que a condição "se vale para todos m < n" é suficiente
    para estabelecer P(n) usando as regras do PIM (Base e Passo). *)

Lemma PIF_to_PIM: PIF -> PIM.
Proof.
  intros h P hbase hsucc.
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

(** -----------------------------------------------------------------
    LEMA 2: Indução Matemática implica Indução Forte
    -----------------------------------------------------------------
    Estratégia: O PIM é "fraco" (só olha para k-1). Para provar o PIF,
    criamos um predicado acumulativo auxiliar:
    "A propriedade P vale para TODOS os números menores que n".
    Se provarmos R(n) por indução padrão, provamos P(n). *)

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

(** -----------------------------------------------------------------
    TEOREMA FINAL
    ----------------------------------------------------------------- *)

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  constructor.
  - exact PIM_to_PIF. (* Usa o Lemma 2 *)
  - exact PIF_to_PIM. (* Usa o Lemma 1 *)
Qed.
