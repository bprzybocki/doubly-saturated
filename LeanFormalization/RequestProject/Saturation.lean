import Mathlib
import RequestProject.Defs

namespace DoublySaturated

/-! # Saturation Lemmas for the Circulant Graph -/

/-
PROBLEM
Given 4 vertices where 5 edges are in G and the 6th is {u,v},
    the graph G ⊔ {edge(u,v)} has a 4-clique.

PROVIDED SOLUTION
Construct the Finset {u, v, x, y} and show it's a 4-clique in G ⊔ fromEdgeSet {s(u,v)}.

¬CliqueFree 4 means ∃ t, IsNClique 4 t. Push negation: simp [CliqueFree, not_forall, Classical.not_not].

Construct t = {u, v, x, y}. Need: t.card = 4 and (G ⊔ fromEdgeSet {s(u,v)}).IsClique ↑t.

For card = 4: all 4 elements distinct. u ≠ v is given. u ≠ x and u ≠ y follow from G.Adj u x and G.Adj u y (adjacency implies inequality by G.loopless). Similarly v ≠ x, v ≠ y, x ≠ y.

For IsClique: for any pair a, b ∈ t with a ≠ b, (G ⊔ fromEdgeSet {s(u,v)}).Adj a b. This is: G.Adj a b ∨ (fromEdgeSet {s(u,v)}).Adj a b. The 5 G-edges are given. The 6th pair {u,v} is in fromEdgeSet.
-/
lemma exhibits_four_clique (m : ℕ) (u v x y : ZMod (6 * m + 1))
    (hux : (G m).Adj u x) (huy : (G m).Adj u y)
    (hvx : (G m).Adj v x) (hvy : (G m).Adj v y) (hxy : (G m).Adj x y)
    (huv : u ≠ v) :
    ¬((G m) ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).CliqueFree 4 := by
  unfold SimpleGraph.CliqueFree; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  use {u, v, x, y};
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ SimpleGraph.fromEdgeSet ];
  · exact hxy.ne;
  · aesop;
  · exact ⟨ hux.1, huy.1 ⟩

/-
PROBLEM
For d ∈ [1, m-1], the vertices {0, d, 2m+1+d, 3m+1+d} provide the 5 edges
    needed by exhibits_four_clique. Plus distinctness.

PROVIDED SOLUTION
For d ∈ [1, m-1], N = 6m+1, w = d, x = 2m+1+d, y = 3m+1+d (as ZMod N elements):

Adjacency checks (unfold G, need u ≠ v and inS m (cyclicNorm N (u - v))):

1. G.Adj 0 x: 0 ≠ x (since x = 2m+1+d ∈ [2m+2, 3m], nonzero mod N).
   cyclicNorm(0-x) = cyclicNorm(-x) = cyclicNorm(x). val(x) = (2m+1+d) % N = 2m+1+d (< N).
   cyclicNorm = min(2m+1+d, N-(2m+1+d)) = min(2m+1+d, 4m-d).
   Since d ≤ m-1: 2m+1+d ≤ 3m, 4m-d ≥ 3m+1. So min = 2m+1+d ∈ [2m+2, 3m] ⊂ [2m+1, 3m]. inS ✓

2. G.Adj 0 y: y = 3m+1+d ∈ [3m+2, 4m]. val(y) = 3m+1+d.
   cyclicNorm = min(3m+1+d, N-(3m+1+d)) = min(3m+1+d, 3m-d).
   Since 3m+1+d > 3m-d, cyclicNorm = 3m-d ∈ [2m+1, 3m-1]. inS ✓

3. G.Adj w x: w = d, x = 2m+1+d. x - w = 2m+1. val(2m+1) = 2m+1.
   cyclicNorm = min(2m+1, 4m) = 2m+1. inS ✓

4. G.Adj w y: w = d, y = 3m+1+d. y - w = 3m+1. val(3m+1) = 3m+1.
   cyclicNorm = min(3m+1, 3m) = 3m. inS ✓

5. G.Adj x y: x = 2m+1+d, y = 3m+1+d. y - x = m. val(m) = m.
   cyclicNorm = min(m, 5m+1) = m. inS (d = m case) ✓

6. 0 ≠ w: d ≥ 1, so d ≠ 0 as ZMod element (since d < N).

For each adjacency, unfold G, split into ≠ and inS. Use ZMod.val_natCast and Nat.mod_eq_of_lt to compute vals. Use omega for arithmetic.
-/
set_option maxHeartbeats 800000 in
lemma case1_witnesses (m : ℕ) (hm : m ≥ 2) (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ m - 1) :
    let N := 6 * m + 1
    let w := (d : ZMod N)
    let x := ((2 * m + 1 + d : ℕ) : ZMod N)
    let y := ((3 * m + 1 + d : ℕ) : ZMod N)
    (G m).Adj 0 x ∧ (G m).Adj 0 y ∧ (G m).Adj w x ∧ (G m).Adj w y ∧ (G m).Adj x y ∧
    (0 : ZMod N) ≠ w := by
  field_simp;
  refine' ⟨ _, _, _, _, _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · norm_cast;
      rw [ eq_comm, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by omega );
    · refine' Or.inr ⟨ _, _ ⟩;
      · rw [ show ( 0 : ZMod ( 6 * m + 1 ) ) - ↑ ( 2 * m + 1 + d ) = ↑ ( 6 * m + 1 - ( 2 * m + 1 + d ) ) by rw [ Nat.cast_sub ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ m ) ] ) ] ; simp +decide ] ; ring_nf;
        unfold cyclicNorm; norm_num [ Nat.add_sub_add_left, show 1 + m * 6 - ( 1 + m * 2 + d ) = m * 4 - d by omega ] ;
        rw [ Nat.mod_eq_of_lt ] <;> omega;
      · simp +arith +decide [ cyclicNorm ];
        exact le_or_gt _ _;
  · refine' ⟨ _, _ ⟩;
    · rw [ Ne.eq_def, eq_comm ];
      rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ m ) ] );
    · -- Let's calculate the cyclic norm of $-(3m + 1 + d)$.
      have h_cyclic_norm : cyclicNorm (6 * m + 1) (-(3 * m + 1 + d) : ZMod (6 * m + 1)) = 3 * m - d := by
        unfold cyclicNorm;
        erw [ ZMod.neg_val ];
        split_ifs <;> norm_cast at *;
        · rw [ ZMod.natCast_eq_zero_iff ] at * ; exact absurd ‹_› ( Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by omega ) );
        · erw [ ZMod.val_natCast ] at *;
          rw [ Nat.mod_eq_of_lt ] <;> omega;
      simp_all +decide [ inS ];
      omega;
  · refine' ⟨ _, _ ⟩;
    · norm_num [ ZMod.natCast_eq_natCast_iff' ];
      norm_cast;
      rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ m ) ] );
    · -- The cyclic norm of -(2m + 1) is 2m + 1, which is in the set S.
      have h_cyclic_norm : cyclicNorm (6 * m + 1) (- (2 * m + 1 : ZMod (6 * m + 1))) = 2 * m + 1 := by
        unfold cyclicNorm;
        have h_neg : (-(2 * m + 1) : ZMod (6 * m + 1)) = (4 * m : ZMod (6 * m + 1)) := by
          rw [ neg_eq_iff_add_eq_zero ] ; ring;
          norm_cast;
          erw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ 1, by ring ⟩;
        norm_num [ h_neg ];
        norm_cast;
        erw [ ZMod.val_cast_of_lt ] <;> norm_num <;> omega;
      simp_all +decide [ add_comm, add_left_comm, add_assoc ];
      exact Or.inr ⟨ by linarith, by omega ⟩;
  · refine' ⟨ _, _ ⟩;
    · rw [ Ne.eq_def, ZMod.natCast_eq_natCast_iff ];
      rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega;
    · unfold cyclicNorm; norm_num [ Nat.mod_eq_of_lt ( by linarith [ Nat.sub_add_cancel hm ] : 3 * m + 1 < 6 * m + 1 ) ] ; ring;
      erw [ ZMod.val_natCast ] ; norm_num ; ring_nf ; norm_num [ Nat.mod_eq_of_lt ( by linarith : 1 + m * 3 < 6 * m + 1 ) ] ;
      erw [ Fin.val_mk, Fin.val_mk ] ; norm_num [ Nat.mod_eq_of_lt ( by linarith : 1 < 1 + m * 6 ) ] ; ring_nf ; norm_num [ Nat.mod_eq_of_lt ( by linarith : 1 < 1 + m * 6 ) ] ;
      norm_num [ show m * 3 % ( 1 + m * 6 ) = m * 3 by rw [ Nat.mod_eq_of_lt ] ; linarith ] ; ring_nf ; norm_num [ Nat.mod_eq_of_lt ( by linarith : 1 < 1 + m * 6 ) ] ;
      rw [ show m * 6 + ( 1 + m * 6 - m * 3 ) = ( 1 + m * 6 ) + ( m * 3 ) by linarith [ Nat.sub_add_cancel ( by linarith : m * 3 ≤ 1 + m * 6 ) ] ] ; norm_num [ Nat.add_mod, Nat.mod_eq_of_lt ( by linarith : 1 + m * 6 > m * 3 ) ] ; ring_nf ; norm_num [ Nat.mod_eq_of_lt ( by linarith : 1 < 1 + m * 6 ) ] ;
      exact Or.inr ⟨ by omega, by omega ⟩;
  · refine' ⟨ _, _ ⟩;
    · refine' ⟨ _, _ ⟩ <;> norm_num [ G ];
      · norm_cast;
        rw [ ZMod.natCast_eq_natCast_iff ];
        rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ m ) ];
      · rw [ show ( 2 * m - 3 * m : ZMod ( 6 * m + 1 ) ) = - ( m : ZMod ( 6 * m + 1 ) ) by ring ];
        rw [ cyclicNorm_neg ];
        unfold cyclicNorm; norm_num [ Nat.mod_eq_of_lt ( by linarith : m < 6 * m + 1 ) ] ;
        exact Or.inl ( by rw [ min_eq_left ] ; omega );
    · norm_num [ ZMod.natCast_eq_natCast_iff' ];
      rw [ eq_comm, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt hd1 ( by omega )

/-
PROBLEM
For d ∈ [m+1, 2m], the vertices {0, d, m+d, 5m+1} provide the 5 edges.

PROVIDED SOLUTION
For d ∈ [m+1, 2m], N = 6m+1, w = d, x = m+d, y = 5m+1 (as ZMod N elements):

1. G.Adj 0 x: val(x) = m+d ∈ [2m+1, 3m]. cyclicNorm = min(m+d, N-(m+d)) = min(m+d, 5m+1-d).
   Since d ≤ 2m: m+d ≤ 3m, 5m+1-d ≥ 3m+1. min = m+d ∈ [2m+1, 3m]. inS ✓

2. G.Adj 0 y: val(y) = 5m+1. cyclicNorm = min(5m+1, m) = m. inS ✓

3. G.Adj w x: x - w = m+d-d = m. cyclicNorm(m) = min(m, 5m+1) = m. inS ✓

4. G.Adj w y: y - w = 5m+1-d. val = 5m+1-d ∈ [3m+1, 4m].
   cyclicNorm = min(5m+1-d, N-(5m+1-d)) = min(5m+1-d, m+d).
   Since 5m+1-d > m+d (for d ≤ 2m): cyclicNorm = m+d ∈ [2m+1, 3m]. inS ✓

5. G.Adj x y: y - x = 5m+1-(m+d) = 4m+1-d ∈ [2m+1, 3m].
   cyclicNorm = min(4m+1-d, N-(4m+1-d)) = min(4m+1-d, 2m+d).
   Since d ≥ m+1: 4m+1-d ≤ 3m, 2m+d ≥ 3m+1. min = 4m+1-d ∈ [2m+1, 3m]. inS ✓

6. 0 ≠ w: d ≥ m+1 ≥ 3 > 0, so d ≠ 0 as ZMod.

For subtraction of nat casts in ZMod: (a : ZMod N) - (b : ZMod N) when a ≥ b as naturals and both < N has val = a - b. Use Nat.cast_sub and ZMod.val_natCast.
-/
set_option maxHeartbeats 800000 in
lemma case2_witnesses (m : ℕ) (hm : m ≥ 2) (d : ℕ) (hd1 : m + 1 ≤ d) (hd2 : d ≤ 2 * m) :
    let N := 6 * m + 1
    let w := (d : ZMod N)
    let x := ((m + d : ℕ) : ZMod N)
    let y := ((5 * m + 1 : ℕ) : ZMod N)
    (G m).Adj 0 x ∧ (G m).Adj 0 y ∧ (G m).Adj w x ∧ (G m).Adj w y ∧ (G m).Adj x y ∧
    (0 : ZMod N) ≠ w := by
  -- Now let's verify each adjacency condition.
  have h0x : (G m).Adj 0 (m + d) := by
    refine' ⟨ _, _ ⟩ <;> norm_cast;
    · rw [ eq_comm, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith );
    · -- Since $d \in [m+1, 2m]$, we have $m + d \in [2m+1, 3m]$, which satisfies the condition for $inS m$.
      have h_cyclicNorm : cyclicNorm (6 * m + 1) (m + d) = m + d := by
        unfold cyclicNorm;
        norm_cast;
        erw [ ZMod.val_cast_of_lt ] <;> norm_num <;> omega;
      simp_all +decide [ Int.subNatNat_eq_coe ];
      rw [ show ( -d + -m : ZMod ( 6 * m + 1 ) ) = - ( m + d ) by ring, cyclicNorm_neg, h_cyclicNorm ] ; exact Or.inr ⟨ by linarith, by linarith ⟩
  have h0y : (G m).Adj 0 (5 * m + 1) := by
    refine' ⟨ _, Or.inl _ ⟩;
    · norm_cast;
      rw [ eq_comm, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith );
    · -- We simplify the expression for the cyclic norm.
      have h_cyclic_norm : cyclicNorm (6 * m + 1) (5 * m + 1) = m := by
        unfold cyclicNorm;
        norm_cast;
        erw [ ZMod.val_cast_of_lt ] <;> norm_num ; omega;
        linarith;
      convert h_cyclic_norm using 1 ; ring;
      convert cyclicNorm_neg _ using 2 ; ring
  have hwxy : (G m).Adj d (m + d) := by
    refine' ⟨ _, _ ⟩ <;> norm_num [ ZMod.natCast_eq_zero_iff ];
    · exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith );
    · -- Since the cyclic norm of $-m$ is $m$, and $m$ is in $S$ by definition, we are done.
      simp [cyclicNorm, inS];
      erw [ ZMod.neg_val ] ; norm_num;
      split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · rw [ ZMod.natCast_eq_zero_iff ] at * ; exact absurd ‹_› ( Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith ) );
      · rw [ Nat.mod_eq_of_lt ] <;> omega
  have hwy : (G m).Adj d (5 * m + 1) := by
    -- The cyclic norm of (5m + 1) - d is min((5m + 1 - d), (6m + 1) - (5m + 1 - d)) = min(5m + 1 - d, m + d).
    have h_cyclic_norm : cyclicNorm (6 * m + 1) ((5 * m + 1 : ZMod (6 * m + 1)) - d) = m + d := by
      unfold cyclicNorm;
      rw [ show ( 5 * m + 1 - d : ZMod ( 6 * m + 1 ) ) = ( 5 * m + 1 - d : ℕ ) from ?_, ZMod.val_natCast ];
      · rw [ Nat.mod_eq_of_lt ] <;> omega;
      · rw [ Nat.cast_sub ] <;> push_cast <;> ring ; linarith;
    -- Since $m + d \in [2m + 1, 3m]$, we have $inS m (m + d)$.
    have h_inS : inS m (m + d) := by
      exact Or.inr ⟨ by linarith, by linarith ⟩;
    constructor;
    · norm_cast at *;
      rw [ ZMod.natCast_eq_natCast_iff ] ; norm_num [ Nat.ModEq, Nat.mod_eq_of_lt ( by linarith : d < 6 * m + 1 ), Nat.mod_eq_of_lt ( by linarith : 5 * m + 1 < 6 * m + 1 ) ] ; omega;
    · rw [ show ( d : ZMod ( 6 * m + 1 ) ) - ( 5 * m + 1 ) = - ( 5 * m + 1 - d ) by ring, cyclicNorm_neg ] ; aesop
  have hxyy : (G m).Adj (m + d) (5 * m + 1) := by
    -- The difference between (m + d) and (5 * m + 1) is 4m + 1 - d, which lies in [2m+1, 3m].
    have h_diff : cyclicNorm (6 * m + 1) ((5 * m + 1 : ZMod (6 * m + 1)) - (m + d)) = 4 * m + 1 - d := by
      have h_diff : (5 * m + 1 : ZMod (6 * m + 1)) - (m + d) = (4 * m + 1 - d : ℕ) := by
        rw [ Nat.cast_sub ] <;> push_cast <;> ring ; linarith;
      rw [ h_diff, cyclicNorm ];
      erw [ ZMod.val_natCast ];
      rw [ Nat.mod_eq_of_lt ] <;> omega;
    refine' ⟨ _, _ ⟩ <;> norm_cast at *;
    · erw [ ZMod.natCast_eq_natCast_iff ] ; norm_num [ Nat.ModEq, Nat.mod_eq_of_lt ( by linarith : m + d < 6 * m + 1 ), Nat.mod_eq_of_lt ( by linarith : 5 * m + 1 < 6 * m + 1 ) ] ; omega;
    · rw [ show ( Int.subNatNat ( m + d ) ( 5 * m + 1 ) : ℤ ) = - ( Int.subNatNat ( 5 * m + 1 ) ( m + d ) ) by rw [ Int.subNatNat_eq_coe, Int.subNatNat_eq_coe ] ; ring ] ; simp_all +decide [ cyclicNorm_neg ];
      rw [ show ( m + d - ( 5 * m + 1 ) : ZMod ( 6 * m + 1 ) ) = - ( 5 * m + 1 - ( m + d ) ) by ring, cyclicNorm_neg ] ; exact h_diff.symm ▸ Or.inr ⟨ by omega, by omega ⟩
  have hne0w : 0 ≠ d := by
    linarith;
  simp_all +decide [ ZMod.natCast_eq_zero_iff ];
  rw [ eq_comm, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith )

/-
PROBLEM
Adding any non-edge to G_m creates a K₄.

PROVIDED SOLUTION
1. Since u ≠ v and ¬G.Adj u v, let w = v - u ≠ 0 with ¬G.Adj 0 w (by G_adj_sub/G_adj_translate).

2. cyclicNorm(w) ∉ S, cyclicNorm ≥ 1 (since w ≠ 0), cyclicNorm ≤ 3m (by cyclicNorm_le). So cyclicNorm ∈ [1,m-1] ∪ [m+1,2m].

3. val(w) is either in [1,m-1], [m+1,2m], [4m+1,5m], or [5m+2,6m] (by inS_cyclicNorm_iff negated).

Case val(w) ∈ [1, m-1]: Apply case1_witnesses with d = val(w). Get 5 G-adjacencies and 0 ≠ w. The vertices are {0, w, x, y}. Apply exhibits_four_clique with u=0, v=w.

Case val(w) ∈ [m+1, 2m]: Apply case2_witnesses with d = val(w). Get 5 G-adjacencies and 0 ≠ w. Apply exhibits_four_clique.

Case val(w) ∈ [4m+1, 5m]: Let w' = -w. Then val(w') = N - val(w) ∈ [m+1, 2m]. Apply case2_witnesses with d = val(w'). Get vertices {0, w', x, y}. Now negate: vertices {0, -w', -x, -y} = {0, w, -x, -y}. By G_adj_translate/negation, the adjacencies are preserved. The edge {0, w} = {0, -w'}. Apply exhibits_four_clique.

Wait, this case is tricky. Let me think... Actually, by the graph's symmetry under negation (since inS is defined in terms of cyclicNorm which is symmetric), G.Adj a b ↔ G.Adj (-a) (-b). So if {0, w', x, y} has the 5 adjacencies, then {0, -w', -x, -y} = {0, w, -x, -y} also has the 5 adjacencies. Then {0, w, -x, -y} with edge {0, w} gives a K₄.

Case val(w) ∈ [5m+2, 6m]: Similarly, let w' = -w with val(w') = N - val(w) ∈ [1, m-1]. Apply case1_witnesses.

For the translation from {0, w} back to {u, v}:
After finding the K₄ with edge {0, w}, translate by +u to get K₄ with edge {u, u+w} = {u, v}. The graph G is circulant so adjacencies are preserved. The edge translates correctly.

So the proof structure:
1. suffices: for any w ≠ 0 with ¬G.Adj 0 w, ¬(G ⊔ fromEdgeSet {s(0,w)}).CliqueFree 4
2. Translate: show the suffices applies to w = v-u
3. Prove the suffices by case analysis on val(w):
   - val(w) ∈ [1,m-1]: use case1_witnesses and exhibits_four_clique
   - val(w) ∈ [m+1,2m]: use case2_witnesses and exhibits_four_clique
   - val(w) ∈ [4m+1,5m] or [5m+2,6m]: use negation to reduce to previous cases

For the negation reduction: if G.Adj 0 x then G.Adj 0 (-x) (since cyclicNorm(-x) = cyclicNorm(x)). More generally, G.Adj a b ↔ G.Adj (-a) (-b) by G_adj_translate with w = -(a+b).

So if {0, d, x, y} has all 5 non-{0,d} edges in G, then {0, -d, -x, -y} has all 5 non-{0,-d} edges in G. Apply exhibits_four_clique with u=0, v=-d.

But -d = w in the cases [4m+1,5m] and [5m+2,6m]. So the edge {0, -d} = {0, w}. ✓

KEY: use the lemma G_adj_translate with w = -u-v to show G.Adj u v ↔ G.Adj (-u) (-v).
-/
set_option maxHeartbeats 1600000 in
lemma add_edge_creates_clique (m : ℕ) (hm : m ≥ 2)
    (u v : ZMod (6 * m + 1)) (huv : u ≠ v) (hnadj : ¬(G m).Adj u v) :
    ¬((G m) ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).CliqueFree 4 := by
  -- By the symmetry of the graph, we can consider the case where $w = v - u$.
  suffices h_symm : ∀ w : ZMod (6 * m + 1), w ≠ 0 → ¬(G m).Adj 0 w → ¬((G m) ⊔ SimpleGraph.fromEdgeSet {s(0, w)}).CliqueFree 4 by
    specialize h_symm ( v - u ) ( sub_ne_zero_of_ne <| Ne.symm huv ) ?_;
    · convert hnadj using 1;
      rw [ G_adj_sub ];
      rw [ G_adj_translate ] ; ring;
    · intro h
      have h_trans : (G m ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) = (G m ⊔ SimpleGraph.fromEdgeSet {s(0, v - u)}).map (Equiv.addRight u) := by
        ext x y; simp +decide [ SimpleGraph.map_adj ] ; ring;
        constructor <;> intro hxy <;> simp_all +decide [ SimpleGraph.adj_comm, SimpleGraph.fromEdgeSet_adj ];
        · use x - u, y - u; simp_all +decide [ SimpleGraph.adj_comm ] ; ring;
          cases hxy <;> simp_all +decide [ sub_eq_iff_eq_add, neg_add_eq_sub ];
          exact Or.inl <| by simpa [ G_adj_sub ] using G_adj_translate m x y ( -u ) |>.1 ‹_›;
        · obtain ⟨ u', v', huv', rfl, rfl ⟩ := hxy; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
          exact Or.imp ( fun h => by simpa [ add_comm ] using G_adj_translate m u' v' u |>.1 h ) id huv'
      simp_all +decide [ SimpleGraph.CliqueFree ];
      obtain ⟨ t, ht ⟩ := h_symm; specialize h ( t.image ( fun x => x + u ) ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      simp_all +decide [ Set.Pairwise, Finset.card_preimage ];
      refine' h _ _;
      · intro x hx y hy hxy; use x + -u, y + -u; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
      · rw [ Finset.filter_true_of_mem fun x hx => ⟨ x + u, by ring ⟩, ht.2 ];
  intro w hw hnw
  by_cases hw_case : ZMod.val w ∈ Finset.Icc 1 (m - 1) ∨ ZMod.val w ∈ Finset.Icc (m + 1) (2 * m) ∨ ZMod.val w ∈ Finset.Icc (4 * m + 1) (5 * m) ∨ ZMod.val w ∈ Finset.Icc (5 * m + 2) (6 * m);
  · rcases hw_case with ( hw_case | hw_case | hw_case | hw_case );
    · obtain ⟨hw1, hw2⟩ : 1 ≤ ZMod.val w ∧ ZMod.val w ≤ m - 1 := by
        aesop;
      obtain ⟨hw3, hw4⟩ : (G m).Adj 0 ((2 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) ∧ (G m).Adj 0 ((3 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) ∧ (G m).Adj w ((2 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) ∧ (G m).Adj w ((3 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) ∧ (G m).Adj ((2 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) ((3 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) := by
        have := case1_witnesses m hm w.val hw1 hw2; aesop;
      apply exhibits_four_clique m 0 w ((2 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) ((3 * m + 1 + w.val : ℕ) : ZMod (6 * m + 1)) hw3 hw4.1 hw4.2.1 hw4.2.2.1 hw4.2.2.2 (by
      exact Ne.symm hw);
    · -- Apply the case2_witnesses lemma to get the 5 edges.
      obtain ⟨hx, hy, hxy, hw⟩ := case2_witnesses m hm (ZMod.val w) (by
      linarith [ Finset.mem_Icc.mp hw_case ]) (by
      linarith [ Finset.mem_Icc.mp hw_case ]);
      convert exhibits_four_clique m 0 w ( m + w.val ) ( 5 * m + 1 ) _ _ _ _ _ _ using 1 <;> simp_all +decide [ SimpleGraph.adj_comm ];
    · -- Let $w' = -w$. Then $w'.val = 6m + 1 - w.val \in [m+1, 2m]$.
      set w' : ZMod (6 * m + 1) := -w
      have hw'_val : w'.val = 6 * m + 1 - w.val := by
        rw [ ZMod.neg_val ];
        aesop
      have hw'_case : w'.val ∈ Finset.Icc (m + 1) (2 * m) := by
        exact Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hw_case, Nat.sub_add_cancel ( show w.val ≤ 6 * m + 1 from by linarith [ Finset.mem_Icc.mp hw_case ] ) ], by linarith [ Finset.mem_Icc.mp hw_case, Nat.sub_add_cancel ( show w.val ≤ 6 * m + 1 from by linarith [ Finset.mem_Icc.mp hw_case ] ) ] ⟩;
      -- Apply case2_witnesses to w' to get the 5 edges.
      obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ZMod (6 * m + 1), (G m).Adj 0 x ∧ (G m).Adj 0 y ∧ (G m).Adj w' x ∧ (G m).Adj w' y ∧ (G m).Adj x y ∧ (0 : ZMod (6 * m + 1)) ≠ w' := by
        have := case2_witnesses m hm w'.val ( Finset.mem_Icc.mp hw'_case |>.1 ) ( Finset.mem_Icc.mp hw'_case |>.2 );
        use (m + w'.val : ZMod (6 * m + 1)), (5 * m + 1 : ZMod (6 * m + 1));
        aesop;
      -- By the symmetry of the graph, we have G.Adj 0 (-x), G.Adj 0 (-y), G.Adj w (-x), G.Adj w (-y), and G.Adj (-x) (-y).
      have h_symm : (G m).Adj 0 (-x) ∧ (G m).Adj 0 (-y) ∧ (G m).Adj w (-x) ∧ (G m).Adj w (-y) ∧ (G m).Adj (-x) (-y) := by
        have h_symm : ∀ a b : ZMod (6 * m + 1), (G m).Adj a b ↔ (G m).Adj (-a) (-b) := by
          intros a b; exact (by
          convert G_adj_translate m a b ( -a - b ) using 1 ; ring;
          exact?);
        exact ⟨ by simpa using h_symm 0 x |>.1 hx, by simpa using h_symm 0 y |>.1 hy, by simpa using h_symm ( -w ) x |>.1 hxy.1, by simpa using h_symm ( -w ) y |>.1 hxy.2.1, by simpa using h_symm x y |>.1 hxy.2.2.1 ⟩;
      -- Apply the lemma exhibits_four_clique to the vertices {0, -x, -y, w} and the edge {0, w}.
      apply exhibits_four_clique m 0 w (-x) (-y);
      all_goals tauto;
    · -- Let $w' = -w$. Then $w'.val = N - w.val \in [1, m-1]$.
      set w' : ZMod (6 * m + 1) := -w
      have hw'_val : w'.val = 6 * m + 1 - w.val := by
        rw [ ZMod.neg_val ] ; aesop;
      have hw'_case : w'.val ∈ Finset.Icc 1 (m - 1) := by
        simp +zetaDelta at *;
        omega
      have hw'_adj : ¬(G m).Adj 0 w' := by
        have hw'_adj : (G m).Adj 0 w' ↔ (G m).Adj 0 w := by
          convert G_adj_sub m 0 ( -w ) using 1 ; ring;
          exact?;
        aesop
      have hw'_clique : ¬((G m) ⊔ SimpleGraph.fromEdgeSet {s(0, w')}).CliqueFree 4 := by
        have hw'_clique : let N := 6 * m + 1; let w := (w'.val : ZMod N); let x := ((2 * m + 1 + w'.val : ℕ) : ZMod N); let y := ((3 * m + 1 + w'.val : ℕ) : ZMod N); (G m).Adj 0 x ∧ (G m).Adj 0 y ∧ (G m).Adj w x ∧ (G m).Adj w y ∧ (G m).Adj x y ∧ (0 : ZMod N) ≠ w := by
          apply case1_witnesses m hm w'.val (Finset.mem_Icc.mp hw'_case).left (Finset.mem_Icc.mp hw'_case).right
        generalize_proofs at *; (
        convert exhibits_four_clique m 0 ( w'.val : ZMod ( 6 * m + 1 ) ) ( ( 2 * m + 1 + w'.val : ℕ ) : ZMod ( 6 * m + 1 ) ) ( ( 3 * m + 1 + w'.val : ℕ ) : ZMod ( 6 * m + 1 ) ) _ _ _ _ _ _ using 1 <;> simp_all +decide [ SimpleGraph.CliqueFree ];
        rw [ ← hw'_val ] ; norm_cast;
        rw [ ZMod.natCast_zmod_val ])
      have hw_clique : ¬((G m) ⊔ SimpleGraph.fromEdgeSet {s(0, w)}).CliqueFree 4 := by
        contrapose! hw'_clique; simp_all +decide [ SimpleGraph.CliqueFree ] ; (
        intro t ht; specialize hw'_clique ( t.image fun x => -x ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        refine' hw'_clique _ _ <;> simp_all +decide [ SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective ];
        refine' hw'_clique _ ; simp_all +decide [ Set.Pairwise, SimpleGraph.fromEdgeSet ] ; (
        intro x hx y hy hxy; specialize ht; have := ht.1 hx hy; simp_all +decide [ SimpleGraph.adj_comm ] ;
        unfold G at *; simp_all +decide [ SimpleGraph.adj_comm ] ;
        rw [ show x - y = - ( -x + y ) by ring, cyclicNorm_neg ] ; aesop;))
      exact hw_clique;
  · -- Since $w \neq 0$ and $¬(G m).Adj 0 w$, we have $cyclicNorm (6 * m + 1) w \notin S$.
    have h_cyclicNorm : ¬inS m (cyclicNorm (6 * m + 1) w) := by
      convert hnw using 1;
      unfold G; simp +decide [ hw, hw_case ] ;
      rw [ eq_comm, cyclicNorm_neg ] ; aesop;
    contrapose! h_cyclicNorm; simp_all +decide [ inS_cyclicNorm_iff ] ;
    by_cases h1 : 1 ≤ w.val <;> by_cases h2 : m < w.val <;> by_cases h3 : 4 * m < w.val <;> by_cases h4 : 5 * m + 2 ≤ w.val <;> simp_all +decide [ Nat.lt_succ_iff ];
    any_goals omega;
    linarith [ show w.val < 6 * m + 1 from w.val_lt ]

end DoublySaturated