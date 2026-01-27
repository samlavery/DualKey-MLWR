(* ============================================================================
   Concrete Vector Algebra Implementation

   Vectors as int lists with proved algebra lemmas.
   These proofs can discharge axioms in VecAlgebra_Abstract.ec
   ============================================================================ *)

require import AllCore List IntDiv.

theory VecConcrete.
  type vec = int list.

  op vec_size (v : vec) : int = size v.

  op vec_add (a b : vec) : vec =
    map (fun p => fst p + snd p) (zip a b).

  op vec_neg (v : vec) : vec =
    map (fun x => -x) v.

  op vec_sub (a b : vec) : vec = vec_add a (vec_neg b).

  (* === PROVED LEMMAS === *)

  (* 1. Commutativity - with size condition *)
  lemma vec_add_comm (a b : vec) :
    vec_size a = vec_size b => vec_add a b = vec_add b a.
  proof.
    rewrite /vec_size.
    elim: a b => [|x xs IH] [|y ys] //= Hsz.
    rewrite /vec_add /=.
    split; first by ring.
    by apply IH; smt().
  qed.

  (* 2. Double negation - unconditional *)
  lemma vec_neg_neg (v : vec) : vec_neg (vec_neg v) = v.
  proof.
    rewrite /vec_neg -map_comp.
    have ->: (fun x => - x) \o (fun x => - x) = fun (x:int) => x by smt().
    by rewrite map_id.
  qed.

  (* 3. Associativity - with size condition *)
  lemma vec_add_assoc (a b c : vec) :
    vec_size a = vec_size b => vec_size b = vec_size c =>
    vec_add (vec_add a b) c = vec_add a (vec_add b c).
  proof.
    rewrite /vec_size.
    elim: a b c => [|x xs IH] [|y ys] [|z zs] //= Hsz1 Hsz2.
    rewrite /vec_add /=.
    split; first by ring.
    by apply IH; smt().
  qed.

  (* 4. Subtraction definition *)
  lemma vec_sub_is_add_neg (a b : vec) :
    vec_sub a b = vec_add a (vec_neg b).
  proof. by rewrite /vec_sub. qed.

end VecConcrete.
