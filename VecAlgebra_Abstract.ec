(* ============================================================================
   Abstract Vector Algebra Theory

   This defines the abstract interface for vector operations.
   Axioms here will be discharged by concrete proofs via theory cloning.
   ============================================================================ *)

require import AllCore List IntDiv.

abstract theory VecAlgebra.
  (* Abstract vector type *)
  type vec.

  (* Size function - needed for conditional lemmas *)
  op vec_size : vec -> int.

  (* Operations *)
  op vec_add : vec -> vec -> vec.
  op vec_neg : vec -> vec.
  op vec_sub (a b : vec) : vec = vec_add a (vec_neg b).

  (* Axioms to be discharged - matching concrete proof signatures *)
  axiom vec_add_comm : forall (a b : vec),
    vec_size a = vec_size b => vec_add a b = vec_add b a.

  axiom vec_neg_neg : forall (v : vec), vec_neg (vec_neg v) = v.

  axiom vec_add_assoc : forall (a b c : vec),
    vec_size a = vec_size b => vec_size b = vec_size c =>
    vec_add (vec_add a b) c = vec_add a (vec_add b c).

  (* Derived lemma - follows from definition *)
  lemma vec_sub_is_add_neg (a b : vec) : vec_sub a b = vec_add a (vec_neg b).
  proof. by rewrite /vec_sub. qed.

end VecAlgebra.
