import Mathlib
import RequestProject.Defs

namespace DoublySaturated

/-! # Removing an edge creates an independent set of size m+2 -/

/-
PROBLEM
Helper: for the case d = m, construct an independent set of size m+2
    in G \ {edge(0, m)}. The set is {6m, 0, 1, ..., m-2, m, 2m-1}
    (which is {-1, 0, 1, ..., m-2, m, 2m-1} in ZMod).

PROVIDED SOLUTION
The independent set in G \ {edge(0, m)} is constructed from natural numbers mapped to ZMod(6m+1):
A_nat = {0, 1, ..., m-2, m, 2*m-1, 6*m} (as natural numbers < 6m+1).

This has m+2 elements: (m-1) elements from {0,...,m-2}, plus m, 2m-1, and 6m = 3 more.

All elements are distinct and < 6m+1. Define A = Finset.image (Nat.cast) A_nat.

For the pairwise check in the complement of G \ {edge(0,m)}: for any x ≠ y in A, either ¬G.Adj x y or {x,y} = {0,m} (the removed edge).

Since all natural number representatives are in [0, 6m], and the "integer" values (treating 6m as -1) lie in [-1, 2m-1], all pairwise absolute differences ≤ 2m. Since 2m < (6m+1)/2 = 3m+0.5, cyclicNorm equals the absolute integer difference.

The absolute integer differences:
- Between elements in {-1, 0, 1, ..., m-2}: at most m-1. Not in S. ✓
- {0, m}: difference m. This IS in S, but it's the removed edge. ✓
- {k, m} for k ∈ {-1, 1, ..., m-2}: m-k ∈ {2, ..., m-1, m+1}. Not m, not in [2m+1, 3m]. ✓
- {k, 2m-1} for k ∈ {-1, 0, ..., m-2}: 2m-1-k ∈ {m+1, ..., 2m}. Not in S. ✓
- {m, 2m-1}: m-1. Not in S. ✓

So the only pair with cyclicNorm in S is {0, m}, which is the removed edge.

Strategy: push_neg to get ∃ t with IsNClique. Construct t. The hardest part is the pairwise adjacency check in the complement. For this, case-split on which elements x, y are. Since the elements come from casting naturals, reduce to arithmetic on naturals.

Key simplification: define the Finset as image of Nat.cast on {0, 1, ..., m-2} ∪ {m, 2*m-1, 6*m} (using Finset.range (m-1) ∪ {m, 2*m-1, 6*m}). Show the cast is injective on this set (all values < 6m+1). Then for the clique check: for any two elements from this nat set, compute their cyclicNorm and verify it's not in S (or it's the removed edge).
-/
set_option maxHeartbeats 1600000 in
lemma remove_edge_case_m (m : ℕ) (hm : m ≥ 2) :
    ¬((G m) \ SimpleGraph.fromEdgeSet
      {s((0 : ZMod (6*m+1)), ((m : ℕ) : ZMod (6*m+1)))})ᶜ.CliqueFree (m + 2) := by
  have h_indep : ∃ t : Finset (ZMod (6 * m + 1)), t.card = m + 2 ∧ ∀ u ∈ t, ∀ v ∈ t, u ≠ v → ¬(G m).Adj u v ∨ (u = 0 ∧ v = m) ∨ (u = m ∧ v = 0) := by
    -- Define the set $t$ as the image of the finset $\{0, 1, \ldots, m-2\} \cup \{m, 2m-1, 6m\}$ under the cast to $ZMod (6m+1)$.
    set t : Finset (ZMod (6 * m + 1)) := Finset.image (fun x : ℕ => x : ℕ → ZMod (6 * m + 1)) (Finset.Ico 0 (m - 1) ∪ {m, 2 * m - 1, 6 * m});
    refine' ⟨ t, _, _ ⟩;
    · rw [ Finset.card_image_of_injOn ];
      · rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.mul_succ ];
      · intros x hx y hy hxy;
        erw [ ZMod.natCast_eq_natCast_iff ] at hxy;
        simp +zetaDelta at *;
        rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at hxy <;> omega;
    · intro u hu v hv huv;
      -- By definition of $t$, we know that $u$ and $v$ are in the image of the finset $\{0, 1, \ldots, m-2\} \cup \{m, 2m-1, 6m\}$ under the cast to $ZMod (6m+1)$.
      obtain ⟨x, hx⟩ : ∃ x ∈ Finset.Ico 0 (m - 1) ∪ {m, 2 * m - 1, 6 * m}, u = x := by
        rw [ Finset.mem_image ] at hu; obtain ⟨ x, hx, rfl ⟩ := hu; exact ⟨ x, hx, rfl ⟩ ;
      obtain ⟨y, hy⟩ : ∃ y ∈ Finset.Ico 0 (m - 1) ∪ {m, 2 * m - 1, 6 * m}, v = y := by
        rw [ Finset.mem_image ] at hv; obtain ⟨ y, hy, rfl ⟩ := hv; exact ⟨ y, hy, rfl ⟩ ;
      -- By definition of $G_m$, we know that $u$ and $v$ are adjacent if and only if their cyclic distance is in $S$.
      have h_adj : (G m).Adj u v ↔ inS m (min (Int.natAbs (x - y : ℤ)) (6 * m + 1 - Int.natAbs (x - y : ℤ))) := by
        have h_cyclicNorm : cyclicNorm (6 * m + 1) (u - v) = min (Int.natAbs (x - y : ℤ)) (6 * m + 1 - Int.natAbs (x - y : ℤ)) := by
          have h_cyclicNorm : ∀ x y : ℕ, x < 6 * m + 1 → y < 6 * m + 1 → cyclicNorm (6 * m + 1) (x - y : ZMod (6 * m + 1)) = min (Int.natAbs (x - y : ℤ)) (6 * m + 1 - Int.natAbs (x - y : ℤ)) := by
            intros x y hx hy
            have h_cyclicNorm : cyclicNorm (6 * m + 1) (x - y : ZMod (6 * m + 1)) = min (Int.natAbs (x - y : ℤ)) (6 * m + 1 - Int.natAbs (x - y : ℤ)) := by
              have h_val : (x - y : ZMod (6 * m + 1)).val = if x ≥ y then x - y else 6 * m + 1 - (y - x) := by
                split_ifs <;> simp_all +decide [ ZMod.val_add, ZMod.val_sub ];
                · norm_cast;
                  erw [ ZMod.val_cast_of_lt ] ; omega;
                · have h_val : (x - y : ZMod (6 * m + 1)) = (6 * m + 1 - (y - x) : ℕ) := by
                    rw [ Nat.cast_sub ( by omega ) ] ; norm_num ; ring;
                    rw [ Nat.cast_sub ( by linarith ) ] ; ring;
                  rw [ h_val, ZMod.val_cast_of_lt ] ; omega
              split_ifs at h_val <;> simp_all +decide [ cyclicNorm ];
              · norm_cast;
              · norm_cast;
                rw [ Int.subNatNat_eq_coe ] ; omega;
            exact h_cyclicNorm;
          rw [ hx.2, hy.2, h_cyclicNorm x y ];
          · simp +zetaDelta at *;
            omega;
          · simp +zetaDelta at *;
            omega;
        unfold G; aesop;
      by_cases hxy : x = 0 ∧ y = m ∨ x = m ∧ y = 0 <;> simp_all +decide [ inS ];
      · rcases hxy with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num at *;
      · omega;
  simp_all +decide [ SimpleGraph.CliqueFree ];
  obtain ⟨ t, ht₁, ht₂ ⟩ := h_indep;
  refine' ⟨ t, _, _ ⟩;
  · intro u hu v hv huv; specialize ht₂ u hu v hv; aesop;
  · exact ht₁

/-
PROBLEM
Helper: for k ∈ [1, m-1], construct an independent set of size m+2
    in G \ {edge(0, 2m+k)}.

PROVIDED SOLUTION
For k ∈ [1, m-1], removing edge {0, 2m+k} creates independent set of size m+2.

The independent set A consists of natural numbers (as ZMod(6m+1)):
A_nat = {0, 2*m, 2*m+k} ∪ {i | k ≤ i ≤ m+k-1, i ≠ m}

The interval [k, m+k-1] has m integers. Since k ≥ 1 and k ≤ m-1, we have m ∈ [k, m+k-1]. Removing m gives m-1 elements. Total: 3 + (m-1) = m+2.

All elements are ≤ 2m+k ≤ 3m-1 < 6m+1. So the cast to ZMod is injective.

The maximum pairwise difference is 2m+k (between 0 and 2m+k). This is the removed edge distance. All other pairwise differences:
- Between 0 and elements in [k, m+k-1]\{m}: difference is in [k, m+k-1]\{m} ⊂ [1, 2m]\{m}. ✓
- Between 0 and 2m: difference is 2m. ∈ [m+1, 2m]. ✓
- Between 0 and 2m+k: difference is 2m+k. THIS IS IN S (since 2m+1 ≤ 2m+k ≤ 3m-1). But it's the removed edge! ✓
- Between 2m and elements in [k, m+k-1]\{m}: 2m - i for i ∈ [k, m+k-1]\{m}. 2m-i ∈ [m-k+1, 2m-k]\{m}. Since k ≥ 1: m-k+1 ≤ m, 2m-k ≥ m+1. Need to check these aren't in S. m-k+1 ∈ [2, m] (but ≠ m when i ≠ m, and m is excluded). So 2m-i ∈ [m-k+1, m-1] ∪ [m+1, 2m-k] ⊂ [1, m-1] ∪ [m+1, 2m]. ✓
- Between 2m and 2m+k: k ∈ [1, m-1]. ✓
- Between 2m+k and elements in [k, m+k-1]\{m}: 2m+k-i for i ∈ [k, m+k-1]\{m}. Range: [m+1, 2m]. ✓
- Between elements in [k, m+k-1]\{m}: |i-j| ∈ [1, m-1]. ✓

So all pairs have cyclicNorm in [1, m-1] ∪ [m+1, 2m] except {0, 2m+k} which is in S.

For the formal proof: construct the Finset as Finset.image Nat.cast (({0, 2*m, 2*m+k} : Finset ℕ) ∪ ((Finset.Icc k (m+k-1)).erase m)). Show card = m+2 and pairwise check.
-/
set_option maxHeartbeats 1600000 in
lemma remove_edge_case_mid (m : ℕ) (hm : m ≥ 2) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ m - 1) :
    ¬((G m) \ SimpleGraph.fromEdgeSet
      {s((0 : ZMod (6*m+1)), ((2*m+k : ℕ) : ZMod (6*m+1)))})ᶜ.CliqueFree (m + 2) := by
  -- Define the set A of natural numbers corresponding to the independent set.
  set A_nat : Finset ℕ := {0, 2 * m, 2 * m + k} ∪ ((Finset.Icc k (m + k - 1)).erase m);
  -- Show that the cast of A_nat to ZMod(6m+1) is injective.
  have h_cast_inj : Finset.card (Finset.image (fun x => x : ℕ → ZMod (6 * m + 1)) A_nat) = Finset.card A_nat := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have : x < 6 * m + 1 ∧ y < 6 * m + 1 := by
      simp +zetaDelta at *;
      omega;
    simp_all +decide [ ZMod.natCast_eq_natCast_iff' ];
    rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at hxy <;> linarith;
  -- Show that the pairwise check in the complement holds for the set A.
  have h_pairwise : ∀ x y : ZMod (6 * m + 1), x ∈ Finset.image (fun x => x : ℕ → ZMod (6 * m + 1)) A_nat → y ∈ Finset.image (fun x => x : ℕ → ZMod (6 * m + 1)) A_nat → x ≠ y → ¬((G m).Adj x y) ∨ (x = 0 ∧ y = (2 * m + k : ZMod (6 * m + 1))) ∨ (x = (2 * m + k : ZMod (6 * m + 1)) ∧ y = 0) := by
    intros x y hx hy hxy
    have h_diff : ∀ x y : ℕ, x ∈ A_nat → y ∈ A_nat → x ≠ y → ¬(inS m (cyclicNorm (6 * m + 1) (x - y : ZMod (6 * m + 1)))) ∨ (x = 0 ∧ y = 2 * m + k) ∨ (x = 2 * m + k ∧ y = 0) := by
      intros x y hx hy hxy
      have h_diff : ∀ x y : ℕ, x ∈ A_nat → y ∈ A_nat → x ≠ y → ¬(inS m (min (Int.natAbs (x - y)) (6 * m + 1 - Int.natAbs (x - y)))) ∨ (x = 0 ∧ y = 2 * m + k) ∨ (x = 2 * m + k ∧ y = 0) := by
        intros x y hx hy hxy
        simp [A_nat] at hx hy hxy ⊢
        by_cases hx0 : x = 0 ∨ x = 2 * m ∨ x = 2 * m + k
        by_cases hy0 : y = 0 ∨ y = 2 * m ∨ y = 2 * m + k
        generalize_proofs at *; (
        rcases hx0 with ( rfl | rfl | rfl ) <;> rcases hy0 with ( rfl | rfl | rfl ) <;> simp +decide [ inS ] at hxy ⊢;
        · norm_cast ; simp +arith +decide [ * ] at * ; omega;
        · omega;
        · exact Or.inl ⟨ by omega, by intros; omega ⟩;
        · exact Or.inl ⟨ by omega, by intros; omega ⟩);
        · rcases hx0 with ( rfl | rfl | rfl ) <;> simp_all +decide [ inS ];
          · omega;
          · constructor <;> omega;
          · constructor <;> omega;
        · unfold inS; simp +decide [ * ] ; omega;
      convert h_diff x y hx hy hxy using 1;
      have h_diff : ∀ x : ℕ, x < 6 * m + 1 → cyclicNorm (6 * m + 1) (x : ZMod (6 * m + 1)) = min x (6 * m + 1 - x) := by
        intros x hx; exact (by
        unfold cyclicNorm; simp +decide [ ZMod.val_cast_of_lt hx ] ;);
      have h_diff : ∀ x y : ℕ, x < 6 * m + 1 → y < 6 * m + 1 → cyclicNorm (6 * m + 1) (x - y : ZMod (6 * m + 1)) = min (Int.natAbs (x - y)) (6 * m + 1 - Int.natAbs (x - y)) := by
        intros x y hx hy
        have h_diff : cyclicNorm (6 * m + 1) (x - y : ZMod (6 * m + 1)) = cyclicNorm (6 * m + 1) (Int.natAbs (x - y) : ZMod (6 * m + 1)) := by
          cases abs_cases ( x - y : ℤ ) <;> simp +decide [ * ];
          rw [ show ( x - y : ZMod ( 6 * m + 1 ) ) = - ( y - x ) by ring, cyclicNorm_neg ];
        convert ‹∀ x : ℕ, x < 6 * m + 1 → cyclicNorm ( 6 * m + 1 ) ↑x = min x ( 6 * m + 1 - x ) › ( Int.natAbs ( x - y ) ) _ using 1;
        cases abs_cases ( x - y : ℤ ) <;> linarith;
      rw [ h_diff x y ( by
        simp +zetaDelta at *;
        omega ) ( by
        simp +zetaDelta at *;
        omega ) ];
    obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx; obtain ⟨ b, hb, rfl ⟩ := Finset.mem_image.mp hy; specialize h_diff a b ha hb; simp_all +decide [ G, inS ] ;
    convert h_diff _;
    · rw [ ZMod.natCast_eq_zero_iff ];
      simp +zetaDelta at *;
      exact ⟨ fun h => Nat.eq_zero_of_dvd_of_lt h ( by omega ), fun h => h.symm ▸ dvd_zero _ ⟩;
    · norm_cast;
      rw [ ZMod.natCast_eq_natCast_iff ];
      simp +zetaDelta at *;
      exact ⟨ fun h => by rw [ Nat.ModEq ] at h; exact by rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at h <;> omega, fun h => by rw [ h ] ⟩;
    · norm_cast;
      erw [ ZMod.natCast_eq_natCast_iff ];
      rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> norm_num;
      · omega;
      · simp +zetaDelta at *;
        omega;
    · simp +zetaDelta at *;
      rw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ fun h => Nat.eq_zero_of_dvd_of_lt h ( by omega ), fun h => h.symm ▸ by norm_num ⟩ ;
    · exact fun h => hxy <| by rw [ h ] ;
  -- Show that the set A is a clique in the complement of G \ {edge(0, 2m+k)}.
  have h_clique : ∀ x y : ZMod (6 * m + 1), x ∈ Finset.image (fun x => x : ℕ → ZMod (6 * m + 1)) A_nat → y ∈ Finset.image (fun x => x : ℕ → ZMod (6 * m + 1)) A_nat → x ≠ y → ((G m \ SimpleGraph.fromEdgeSet {s(0, (2 * m + k : ZMod (6 * m + 1)))})ᶜ).Adj x y := by
    intro x y hx hy hxy; specialize h_pairwise x y hx hy hxy; simp_all +decide [ SimpleGraph.compl_adj ] ;
    tauto;
  -- Show that the set A has cardinality m+2.
  have h_card : Finset.card (Finset.image (fun x => x : ℕ → ZMod (6 * m + 1)) A_nat) = m + 2 := by
    rw [ h_cast_inj, Finset.card_union_of_disjoint ] <;> norm_num;
    · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num;
      · rw [ Finset.card_erase_of_mem ] <;> norm_num;
        · omega;
        · omega;
      · linarith;
      · exact ⟨ by linarith, by linarith ⟩;
    · exact ⟨ fun _ => by linarith, fun _ _ => by omega, fun _ => by omega ⟩;
  simp_all +decide [ SimpleGraph.CliqueFree ];
  refine' ⟨ Finset.image ( fun x : ℕ => x : ℕ → ZMod ( 6 * m + 1 ) ) A_nat, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
  intro x hx y hy hxy; simp_all +decide [ SimpleGraph.adj_comm ] ;
  exact h_clique x y _ hx.choose_spec.1 hx.choose_spec.2 _ hy.choose_spec.1 hy.choose_spec.2 hxy

/-
PROBLEM
Helper: for d = 3m, construct an independent set of size m+2
    in G \ {edge(0, 3m)}.

PROVIDED SOLUTION
We need to show that removing the edge {0, 3m} from G creates an independent set of size m+2 in G \ {edge(0, 3m)}.

Equivalently, we need ¬((G m) \ fromEdgeSet {s(0, 3m)})ᶜ.CliqueFree (m+2), meaning there IS a clique of size m+2 in the complement of G \ {edge(0, 3m)}.

The complement of G \ {edge} at vertices u, v is: u ≠ v ∧ (¬G.Adj u v ∨ {u,v} = {0, 3m}).

The independent set is A = {4m+1, 4m+2, ..., 5m} ∪ {0, 3m} (as ZMod(6m+1) values). Note -2m ≡ 4m+1, -2m+1 ≡ 4m+2, ..., -m-1 ≡ 5m (mod 6m+1). And 3m is in the set.

|A| = m + 2. For all pairs u, v ∈ A with u ≠ v:
- If {u,v} = {0, 3m}: this is the removed edge, so they're non-adjacent in G \ {edge}. In the complement, they ARE adjacent. ✓
- If u, v ∈ {4m+1, ..., 5m}: |u - v| ≤ m - 1, cyclicNorm = |u-v| ∈ [1, m-1] ⊂ Sᶜ. ✓
- If u = 0, v ∈ {4m+1, ..., 5m}: cyclicNorm(v) = N - v = 6m+1 - v ∈ [m+1, 2m]. ∈ Sᶜ. ✓
- If u = 3m, v ∈ {4m+1, ..., 5m}: v - 3m ∈ [m+1, 2m]. cyclicNorm = N - (v-3m) = 6m+1-(v-3m) = 9m+1-v. For v ∈ [4m+1, 5m]: 9m+1-v ∈ [4m+1, 5m]. So cyclicNorm = min(v-3m, 9m+1-v). Since v-3m ∈ [m+1, 2m] and 9m+1-v ∈ [4m+1, 5m], min = v-3m ∈ [m+1, 2m] ⊂ Sᶜ. ✓

So all pairs are non-adjacent in G (except {0,3m} which is the removed edge), hence they form a clique in the complement of G \ {edge}.

For the formal proof: construct the Finset as (Finset.Icc (4*m+1) (5*m)).map (some embedding to ZMod) ∪ {0, 3m}. Actually, use Finset.image (fun i => (i : ZMod (6*m+1))) on a range.

This is quite involved. Use simp and omega for the individual distance checks.
-/
set_option maxHeartbeats 1600000 in
lemma remove_edge_case_3m (m : ℕ) (hm : m ≥ 2) :
    ¬((G m) \ SimpleGraph.fromEdgeSet
      {s((0 : ZMod (6*m+1)), ((3*m : ℕ) : ZMod (6*m+1)))})ᶜ.CliqueFree (m + 2) := by
  unfold SimpleGraph.CliqueFree;
  simp +decide [ SimpleGraph.isNClique_iff ];
  refine' ⟨ Finset.image ( fun i : ℕ => ( 4 * m + 1 + i : ZMod ( 6 * m + 1 ) ) ) ( Finset.range m ) ∪ { 0, ( 3 * m : ZMod ( 6 * m + 1 ) ) }, _, _ ⟩ <;> simp +decide [ SimpleGraph.IsIndepSet ];
  · intro x hx y hy hxy; simp_all +decide [ Finset.mem_insert, Finset.mem_image ] ;
    unfold G; simp_all +decide [ SimpleGraph.adj_comm ] ;
    rcases hx with ( rfl | rfl | ⟨ i, hi, rfl ⟩ ) <;> rcases hy with ( rfl | rfl | ⟨ j, hj, rfl ⟩ ) <;> norm_num at *;
    · unfold cyclicNorm; norm_cast; simp +decide [ *, Nat.add_mod, Nat.mul_mod ] ;
      rw [ show ( -j + ( -1 + - ( 4 * m ) ) : ZMod ( 6 * m + 1 ) ) = - ( 4 * m + j + 1 ) by ring ];
      erw [ ZMod.neg_val ] ; norm_cast ; simp +decide [ *, Nat.add_mod, Nat.mul_mod ];
      split_ifs <;> norm_cast at * ; simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
      · norm_cast at *;
        rw [ ZMod.natCast_eq_zero_iff ] at * ; exact absurd ‹_› ( Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith ) );
      · erw [ ZMod.val_cast_of_lt ] at * <;> try linarith;
        unfold inS; norm_num; omega;
    · unfold cyclicNorm; norm_cast; simp +decide [ *, Nat.add_mod, Nat.mul_mod ] ;
      -- Let's simplify the expression for the cyclic norm.
      have h_cyclic_norm : (3 * m - (4 * m + 1 + j) : ZMod (6 * m + 1)).val = 5 * m - j := by
        have h_cyclic_norm : (3 * m - (4 * m + 1 + j) : ZMod (6 * m + 1)).val = (6 * m + 1 - (m + 1 + j)) % (6 * m + 1) := by
          rw [ show ( 3 * m - ( 4 * m + 1 + j ) : ZMod ( 6 * m + 1 ) ) = ( 6 * m + 1 - ( m + 1 + j ) : ZMod ( 6 * m + 1 ) ) by
                ring;
                rw [ show ( -1 : ZMod ( 6 * m + 1 ) ) = 6 * m by rw [ neg_eq_iff_add_eq_zero ] ; norm_cast ; simp +arith +decide ] ; ring ];
          norm_cast;
          rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast;
        rw [ h_cyclic_norm, Nat.mod_eq_of_lt ] <;> omega;
      unfold inS; simp_all +decide [ Nat.sub_sub ] ;
      omega;
    · unfold inS cyclicNorm; norm_cast; simp_all +decide [ Nat.mod_eq_of_lt ] ;
      norm_cast at *;
      erw [ ZMod.val_cast_of_lt ] <;> norm_num <;> omega;
    · unfold inS; norm_cast; simp_all +decide [ cyclicNorm ] ;
      ring_nf; norm_cast; simp_all +decide [ ZMod.val_add, ZMod.val_mul ] ;
      rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ ZMod.val ];
      rw [ Nat.mod_eq_of_lt ] <;> omega;
    · unfold inS; simp_all +decide [ cyclicNorm ] ;
      -- Since $i$ and $j$ are both less than $m$, the difference $i - j$ is between $-m$ and $m$. Therefore, $|i - j| \leq m - 1$.
      have h_diff : (i - j : ZMod (6 * m + 1)).val ≤ m - 1 ∨ (i - j : ZMod (6 * m + 1)).val ≥ 5 * m + 2 := by
        have h_diff : (i - j : ℤ) % (6 * m + 1) ≤ m - 1 ∨ (i - j : ℤ) % (6 * m + 1) ≥ 5 * m + 2 := by
          by_cases h_case : (i - j : ℤ) < 0;
          · rw [ Int.emod_eq_add_self_emod ];
            rw [ Int.emod_eq_of_lt ] <;> omega;
          · exact Or.inl ( by rw [ Int.emod_eq_of_lt ] <;> linarith );
        convert h_diff using 1;
        · erw [ ← ZMod.val_intCast ] ; norm_num [ Int.subNatNat_eq_coe ] ; ring;
          erw [ ZMod.cast_eq_val ] ; norm_cast;
          exact ⟨ fun h => lt_of_le_of_lt h ( Nat.pred_lt ( ne_bot_of_gt hm ) ), fun h => Nat.le_pred_of_lt h ⟩;
        · erw [ ← ZMod.val_intCast ] ; norm_cast;
      omega;
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num;
    · rw [ Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
      intro i hi j hj hij; simp_all +decide [ ZMod.natCast_eq_natCast_iff ] ;
      rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at hij <;> linarith;
    · norm_cast;
      intro x hx; erw [ ZMod.natCast_eq_natCast_iff ] ; norm_num [ Nat.modEq_iff_dvd ] ;
      exact fun ⟨ k, hk ⟩ => by nlinarith [ show k = 0 by nlinarith ] ;
    · norm_cast;
      rw [ eq_comm, ZMod.natCast_eq_zero_iff ];
      exact ⟨ Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith ), fun x hx => by rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by linarith ) ( by linarith ) ⟩

/-
PROBLEM
Removing any edge from G_m creates an independent set of size m+2.

PROVIDED SOLUTION
By translation invariance (G_adj_translate), WLOG one endpoint is 0. Specifically, let w = v - u. Then G.Adj u v ↔ G.Adj 0 w (by G_adj_sub). And it suffices to prove the result for the edge {0, w}.

By G_adj_sub and the definition of G, G.Adj 0 w means w ≠ 0 and cyclicNorm(w) ∈ S = {m} ∪ [2m+1, 3m]. By inS_cyclicNorm_iff, w.val ∈ {m, 5m+1} ∪ [2m+1, 4m].

By the symmetry of the graph under negation (G.Adj a b ↔ G.Adj (-a) (-b)), we can assume WLOG that w.val ∈ {m} ∪ [2m+1, 3m] (the "positive" half of D). If w.val ∈ {5m+1} ∪ [3m+1, 4m], replace w by -w (which has val in {m} ∪ [2m+1, 3m]).

Case 1: w.val = m → apply remove_edge_case_m.
Case 2: w.val ∈ [2m+1, 3m-1] → w.val = 2m + k with k = w.val - 2m ∈ [1, m-1] → apply remove_edge_case_mid with this k.
Case 3: w.val = 3m → apply remove_edge_case_3m.

For the translation: if removing edge {0, d} from G creates an independent set of size m+2 in (G \ {edge(0,d)})ᶜ, then removing edge {u, v} = {u, u+d} creates an independent set of size m+2 in (G \ {edge(u, v)})ᶜ, by translating the independent set by u. The graph G is circulant (translation-invariant), so translating a clique in the complement gives a clique in the complement.

For the negation: G \ {edge(0, w)} and G \ {edge(0, -w)} have the same complement clique structure, since negating all vertices preserves G (by cyclicNorm_neg) and maps {0, w} to {0, -w}.

This requires showing:
1. (G m \ fromEdgeSet {s(0, w)})ᶜ ≅ (G m \ fromEdgeSet {s(u, v)})ᶜ (via translation by u)
2. (G m \ fromEdgeSet {s(0, w)})ᶜ ≅ (G m \ fromEdgeSet {s(0, -w)})ᶜ (via negation)

The formal argument: if ¬CliqueFree k for one, then ¬CliqueFree k for the other (map the clique finset via the translation/negation automorphism).

Use the translation: the map x ↦ x + u is a bijection preserving G-adjacency and mapping edge {0, w} to edge {u, u+w} = {u, v}. Similarly, x ↦ -x preserves G-adjacency and maps {0, w} to {0, -w}.
-/
set_option maxHeartbeats 1600000 in
lemma remove_edge_creates_indep (m : ℕ) (hm : m ≥ 2)
    (u v : ZMod (6 * m + 1)) (hadj : (G m).Adj u v) :
    ¬((G m) \ SimpleGraph.fromEdgeSet {s(u, v)})ᶜ.CliqueFree (m + 2) := by
  -- By translation invariance, we can assume without loss of generality that $u = 0$.
  suffices h_trans : ∀ v : ZMod (6 * m + 1), (G m).Adj 0 v → ¬((G m) \ SimpleGraph.fromEdgeSet {s(0, v)})ᶜ.CliqueFree (m + 2) by
    -- By translation invariance, we can assume without loss of generality that $u = 0$ and $v$ is some element in $ZMod (6 * m + 1)$.
    obtain ⟨v', hv'⟩ : ∃ v', (G m).Adj 0 v' ∧ v = u + v' := by
      use v - u;
      rw [ G_adj_sub ] at * ; aesop;
    specialize h_trans v' hv'.1;
    simp_all +decide [ SimpleGraph.CliqueFree ];
    obtain ⟨ x, hx ⟩ := h_trans;
    use x.image (fun y => y + u);
    simp_all +decide [ SimpleGraph.isNIndepSet_iff, SimpleGraph.fromEdgeSet ];
    simp_all +decide [ SimpleGraph.IsIndepSet, Finset.card_image_of_injective, Function.Injective ];
    simp_all +decide [ Set.Pairwise, Finset.card_preimage ];
    constructor;
    · intro a ha b hb hab h; specialize hx; have := hx.1 ha hb; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      specialize this ( by
        convert G_adj_translate m a b ( -u ) using 1 ; ring;
        simp_all +decide [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ] ) ; aesop;
    · convert hx.2 using 2;
      exact Finset.filter_true_of_mem fun y hy => ⟨ y + u, by ring ⟩;
  intro v hv
  obtain ⟨k, hk⟩ : ∃ k, ZMod.val v = k ∧ (k = m ∨ 2 * m + 1 ≤ k ∧ k ≤ 3 * m ∨ k = 5 * m + 1 ∨ 3 * m + 1 ≤ k ∧ k ≤ 4 * m) := by
    have h_cyclicNorm : inS m (cyclicNorm (6 * m + 1) v) := by
      convert hv.2 using 1;
      simp +decide [ cyclicNorm_neg ];
    by_cases hv_zero : v = 0 <;> simp_all +decide [ inS_cyclicNorm_iff ];
    omega;
  rcases hk with ⟨ hk₁, hk₂ | hk₂ | hk₂ | hk₂ ⟩;
  · convert remove_edge_case_m m hm using 1;
    rw [ show v = ↑m from by rw [ ← ZMod.natCast_zmod_val v, hk₁, hk₂ ] ];
  · -- If $2m+1 \leq k \leq 3m-1$, then we can apply the lemma `remove_edge_case_mid`.
    by_cases hk3 : k ≤ 3 * m - 1;
    · convert remove_edge_case_mid m hm ( k - 2 * m ) ( Nat.sub_pos_of_lt ( by omega ) ) ( Nat.sub_le_of_le_add ( by omega ) ) using 1;
      rw [ show ( 2 * m + ( k - 2 * m ) : ℕ ) = k by rw [ add_tsub_cancel_of_le ( by linarith ) ] ];
      rw [ ← hk₁, ZMod.natCast_zmod_val ];
    · -- If $k = 3m$, then we can apply the lemma `remove_edge_case_3m`.
      have hk4 : k = 3 * m := by
        omega;
      convert remove_edge_case_3m m hm using 1;
      rw [ ← hk4, ← ZMod.natCast_zmod_val v ] ; aesop;
  · -- By symmetry of the graph under negation, we can replace $v$ with $-v$.
    have h_neg : ¬((G m) \ SimpleGraph.fromEdgeSet {s(0, -v)})ᶜ.CliqueFree (m + 2) := by
      have h_neg : ZMod.val (-v) = m := by
        rw [ ZMod.neg_val ];
        split_ifs <;> simp_all +decide [ ZMod.val_eq_one ] ; omega;
      convert remove_edge_case_m m hm using 1;
      simp +decide [ ← h_neg, ZMod.natCast_zmod_val ];
    convert h_neg using 1;
    constructor <;> intro h <;> simp_all +decide [ SimpleGraph.CliqueFree ];
    intro t ht; specialize h ( t.image fun x => -x ) ; simp_all +decide [ SimpleGraph.isNIndepSet_iff ] ;
    refine' h _ _;
    · intro x hx y hy hxy; simp_all +decide [ SimpleGraph.fromEdgeSet ] ;
      have := ht.1 hx hy; simp_all +decide [ SimpleGraph.adj_comm ] ;
      convert this using 1;
      unfold G; simp +decide [ SimpleGraph.adj_comm ] ;
      rw [ show -x + y = - ( x - y ) by ring, cyclicNorm_neg ] ; aesop;
    · rw [ Finset.card_image_of_injective _ neg_injective, ht.2 ];
  · -- By negation, we can assume without loss of generality that $v.val \in \{m\} \cup [2m+1, 3m]$.
    have h_neg : ¬((G m) \ SimpleGraph.fromEdgeSet {s(0, -v)})ᶜ.CliqueFree (m + 2) := by
      by_cases h_case : ZMod.val (-v) = m ∨ 2 * m + 1 ≤ ZMod.val (-v) ∧ ZMod.val (-v) ≤ 3 * m;
      · cases' h_case with h_case h_case;
        · convert remove_edge_case_m m hm using 1;
          rw [ ← ZMod.natCast_zmod_val ( -v ), h_case ];
        · by_cases h_case : ZMod.val (-v) = 3 * m;
          · convert remove_edge_case_3m m hm using 1;
            rw [ ← h_case ];
            rw [ ZMod.natCast_zmod_val ];
          · -- Since $(-v).val \in [2m+1, 3m-1]$, we can apply the lemma remove_edge_case_mid.
            obtain ⟨k, hk⟩ : ∃ k, 1 ≤ k ∧ k ≤ m - 1 ∧ ZMod.val (-v) = 2 * m + k := by
              exact ⟨ ( -v |> ZMod.val ) - 2 * m, Nat.sub_pos_of_lt ( by omega ), Nat.sub_le_of_le_add ( by omega ), by omega ⟩;
            convert remove_edge_case_mid m hm k hk.1 hk.2.1 using 1;
            rw [ ← hk.2.2 ];
            rw [ ZMod.natCast_zmod_val ];
      · have h_neg : ZMod.val (-v) = 6 * m + 1 - k := by
          haveI := Fact.mk ( by linarith : 1 < 6 * m + 1 ) ; erw [ ZMod.neg_val ] ; aesop;
        omega;
    contrapose! h_neg;
    intro t ht; specialize h_neg ( t.image fun x => -x ) ; simp_all +decide [ SimpleGraph.comap, SimpleGraph.fromEdgeSet ] ;
    simp_all +decide [ SimpleGraph.isNIndepSet_iff, Finset.card_image_of_injective, Function.Injective ];
    simp_all +decide [ SimpleGraph.IsIndepSet, Set.Pairwise ];
    obtain ⟨ x, hx, y, hy, hxy, hxy', hx', hy' ⟩ := h_neg; specialize ht; have := ht.1 hx hy; simp_all +decide [ SimpleGraph.adj_comm ] ;
    simp_all +decide [ G ];
    simp_all +decide [ neg_add_eq_sub, cyclicNorm_neg ];
    exact absurd ( this ( by rw [ show y - x = - ( x - y ) by ring, cyclicNorm_neg ] ; exact hxy' ) ) ( by aesop )

end DoublySaturated