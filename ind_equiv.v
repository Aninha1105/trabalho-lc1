(** * Equivalência entre o Princípio da Indução Matemática e o Princípio da Indução Forte *)

Require Import Arith.

(** Seja [P] uma propriedade sobre os números naturais. O Princípio da *)
(** Indução Matemática (PIM) pode ser enunciado da seguinte forma:  *)

Definition PIM :=
  forall P: nat -> Prop,
    (P 0) ->
    (forall k, P k -> P (S k)) ->
    forall n, P n.

(** Seja [Q] uma propriedade sobre os números naturais. O Princípio da *)
(** Indução Forte (PIF) pode ser enunciado da seguinte forma:  *)

Definition PIF :=
  forall Q: nat -> Prop,
    (forall k, (forall m, m<k -> Q m) -> Q k) ->
    forall n, Q n.

(** Prove que estes princípios são equivalentes: *)

Lemma PIF_to_PIM: PIF -> PIM.
Proof.
(* Substitua esta linha pela sua prova*) Admitted.

Lemma PIM_to_PIF: PIM -> PIF.
Proof.
(* Substitua esta linha pela sua prova*) Admitted.

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  (* Substitua esta linha pela sua prova*) Admitted.
