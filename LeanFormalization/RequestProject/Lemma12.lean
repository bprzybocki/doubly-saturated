import Mathlib
import RequestProject.Defs

namespace DoublySaturated

/-! # Lemma 1: G_m is K₄-free, and Lemma 2: No independent set of size m+2 -/

/-
PROBLEM
Core gap impossibility.

PROVIDED SOLUTION
Pure arithmetic impossibility. We have g1+g2+g3+g4 = 6m+1 where m ≥ 2, each gi is either m, 5m+1, or in [2m+1, 4m], and no two adjacent (cyclically) gaps are both m (h12, h23, h34, h41 prevent g1=g2=m, g2=g3=m, g3=g4=m, g4=g1=m).

Step 1: No gi = 5m+1. If say g1 = 5m+1, then g2+g3+g4 = m. But each gi ≥ m, so g2+g3+g4 ≥ 3m > m. Contradiction.

Step 2: So each gi ∈ {m} ∪ [2m+1, 4m].

Step 3: At most 1 gap equals m is impossible: if ≤ 1 gap is m, then ≥ 3 gaps are ≥ 2m+1. Sum ≥ 3(2m+1) + 0 = 6m+3 > 6m+1 (even adding 0 for the possible m-gap). If exactly 1 is m: sum ≥ m + 3(2m+1) = 7m+3 > 6m+1. If 0 are m: sum ≥ 4(2m+1) = 8m+4 > 6m+1.

Step 4: So ≥ 2 gaps equal m. By the adjacency constraints, they can't be adjacent. With 4 gaps in a cycle, two non-adjacent means g1=g3=m or g2=g4=m. But if exactly 2 are m: remaining 2 sum to 4m+1, each ≥ 2m+1, so sum ≥ 2(2m+1) = 4m+2 > 4m+1.

If 3 are m: any 3 consecutive includes an adjacent pair of m's. And sum would be 3m + g ≥ 3m + 2m+1 = 5m+1 or 3m+m = 4m. For 3m+g4 = 6m+1, g4 = 3m+1 ∈ [2m+1,4m] ✓. But if g1=g2=g3=m, then g1=g2=m violates h12. Any arrangement of 3 m's has adjacent pair.

If 4 are m: 4m = 6m+1 impossible since m ≥ 2.

All cases lead to omega contradictions after enough case splitting.
-/
lemma no_four_gaps (m : ℕ) (hm : m ≥ 2) (g₁ g₂ g₃ g₄ : ℕ)
    (hg₁ : g₁ = m ∨ g₁ = 5 * m + 1 ∨ (2 * m + 1 ≤ g₁ ∧ g₁ ≤ 4 * m))
    (hg₂ : g₂ = m ∨ g₂ = 5 * m + 1 ∨ (2 * m + 1 ≤ g₂ ∧ g₂ ≤ 4 * m))
    (hg₃ : g₃ = m ∨ g₃ = 5 * m + 1 ∨ (2 * m + 1 ≤ g₃ ∧ g₃ ≤ 4 * m))
    (hg₄ : g₄ = m ∨ g₄ = 5 * m + 1 ∨ (2 * m + 1 ≤ g₄ ∧ g₄ ≤ 4 * m))
    (hsum : g₁ + g₂ + g₃ + g₄ = 6 * m + 1)
    (h12 : ¬(g₁ = m ∧ g₂ = m)) (h23 : ¬(g₂ = m ∧ g₃ = m))
    (h34 : ¬(g₃ = m ∧ g₄ = m)) (h41 : ¬(g₄ = m ∧ g₁ = m)) : False := by
  grind +qlia

/-
PROVIDED SOLUTION
We have 4 pairwise adjacent vertices a, b, c, d in G_m. By vertex-transitivity (G_adj_translate), WLOG a = 0. So b, c, d are nonzero with pairwise edges.

The key idea: order b, c, d by their ZMod.val values and define the "gaps" between consecutive elements around the circle. Since all 6 pairs are adjacent, all pairwise differences are in the directed edge set D. The gaps sum to N = 6m+1.

More precisely, by G_adj_sub, G.Adj x y iff cyclicNorm(x-y) ∈ S. By inS_cyclicNorm_iff, this means val(x-y) is in D = {m, 5m+1} ∪ [2m+1, 4m].

For 4 vertices on the circle, there are 4 gaps g₁, g₂, g₃, g₄ (between consecutive vertices in cyclic order) summing to N. Each gap is the val of some difference, so each gi ∈ D.

Additionally, consecutive gaps g_i + g_{i+1} correspond to the val of a "skipped" difference, which must also be in D ∪ {0}, but actually must be nonzero and in D since all pairs are adjacent.

The constraint "adjacent gaps can't both be m": if gi = g_{i+1} = m, the sum gi + g_{i+1} = 2m, and the vertex pair spanning both gaps has val of difference = 2m, but 2m ∉ D (since m < 2m < 2m+1). So that pair wouldn't be adjacent. Contradiction.

Apply no_four_gaps to conclude False.

Actually implementing this: we need to sort the 4 values of val(a), val(b), val(c), val(d) on the circle. Since a = 0 (WLOG), the gaps between sorted values of val(b), val(c), val(d) and 0 give the 4 cyclic gaps. Each gap is the val of a difference between consecutive sorted vertices, hence is in D. And adjacent gaps summing to a non-D value gives contradiction.

This is complex. An alternative: use the translation invariance to set a = 0. Then work with val(b), val(c), val(d). The 6 edges give 6 constraints on these values (each pairwise val difference mod N must be in D). Use inS_cyclicNorm_iff for each. Then apply no_four_gaps.

Actually, the formal argument with sorting is complex. Let me simplify: we don't need to sort. We can directly use:
- The 6 pairwise differences (as ZMod vals) are all in D.
- Consider the 4 values mod N. Pick the cyclic ordering. The 4 gaps sum to N and are each in D (since they're differences of adjacent-in-cycle vertices, which are also pairwise adjacent in G). The gaps between "every other" vertex must also be in D. Adjacent gaps both being m forces a sum of 2m ∉ D.

This is getting involved. Let me just trust the subagent with the arithmetic: after substituting a = 0 and getting val(b), val(c), val(d) ∈ D, and all pairwise (mod N) differences in D, derive False using no_four_gaps.
-/
set_option maxHeartbeats 800000 in
/-- No 4 pairwise adjacent vertices in G_m. -/
lemma no_four_clique (m : ℕ) (hm : m ≥ 2)
    (a b c d : ZMod (6 * m + 1))
    (hab : (G m).Adj a b) (hac : (G m).Adj a c) (had : (G m).Adj a d)
    (hbc : (G m).Adj b c) (hbd : (G m).Adj b d) (hcd : (G m).Adj c d) :
    False := by
  -- By translation invariance, we can assume without loss of generality that $a = 0$.
  wlog ha : a = 0 generalizing a b c d;
  · apply this (a - a) (b - a) (c - a) (d - a);
    all_goals have := G_adj_translate m a b ( -a ) ; have := G_adj_translate m a c ( -a ) ; have := G_adj_translate m a d ( -a ) ; have := G_adj_translate m b c ( -a ) ; have := G_adj_translate m b d ( -a ) ; have := G_adj_translate m c d ( -a ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
    all_goals simp_all +decide [ sub_eq_add_neg ] ;
  · -- By vertex-transitivity, we can assume without loss of generality that $b = 0$.
    subst ha;
    -- By the properties of the cyclic norm and the definition of adjacency in $G_m$, we know that $b$, $c$, and $d$ must satisfy certain conditions.
    have h_bc : ZMod.val b = m ∨ ZMod.val b = 5 * m + 1 ∨ (2 * m + 1 ≤ ZMod.val b ∧ ZMod.val b ≤ 4 * m) := by
      have := hab.2;
      rw [ show ( 0 - b : ZMod ( 6 * m + 1 ) ) = -b by ring, cyclicNorm_neg ] at this;
      exact inS_cyclicNorm_iff m b ( by aesop_cat ) |>.1 this
    have h_cd : ZMod.val c = m ∨ ZMod.val c = 5 * m + 1 ∨ (2 * m + 1 ≤ ZMod.val c ∧ ZMod.val c ≤ 4 * m) := by
      have := inS_cyclicNorm_iff m ( 0 - c ) ; simp_all +decide [ G ] ;
      by_cases hc : c = 0 <;> simp_all +decide [ ZMod.neg_val ];
      omega
    have h_bd : ZMod.val d = m ∨ ZMod.val d = 5 * m + 1 ∨ (2 * m + 1 ≤ ZMod.val d ∧ ZMod.val d ≤ 4 * m) := by
      apply (inS_cyclicNorm_iff m d (by
      exact fun h => by simp_all +decide [ G ] ;)).mp;
      convert had.2 using 1;
      simp +decide [ cyclicNorm_neg ]
    have h_bc_cd : ZMod.val (c - b) = m ∨ ZMod.val (c - b) = 5 * m + 1 ∨ (2 * m + 1 ≤ ZMod.val (c - b) ∧ ZMod.val (c - b) ≤ 4 * m) := by
      have h_bc_cd : inS m (cyclicNorm (6 * m + 1) (c - b)) := by
        have h_bc_cd : (G m).Adj (c - b) 0 := by
          convert G_adj_sub m c b using 1;
          exact iff_of_true ( by simpa [ G_adj_sub ] using hbc.symm ) ( iff_of_true ( by simpa [ G_adj_sub ] using hbc.symm ) ( by simpa [ G_adj_sub ] using hbc.symm ) );
        convert h_bc_cd.2 using 1;
        norm_num;
      apply inS_cyclicNorm_iff m (c - b) (by
      exact sub_ne_zero_of_ne <| by rintro rfl; exact hbc.1 rfl;) |>.1 h_bc_cd
    have h_bd_cd : ZMod.val (d - b) = m ∨ ZMod.val (d - b) = 5 * m + 1 ∨ (2 * m + 1 ≤ ZMod.val (d - b) ∧ ZMod.val (d - b) ≤ 4 * m) := by
      have h_bd_cd : inS m (cyclicNorm (6 * m + 1) (d - b)) := by
        convert hbd.2 using 1;
        rw [ ← neg_sub, cyclicNorm_neg ];
      apply (inS_cyclicNorm_iff m (d - b) (by
      intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;)).mp h_bd_cd
    have h_cd_bd : ZMod.val (d - c) = m ∨ ZMod.val (d - c) = 5 * m + 1 ∨ (2 * m + 1 ≤ ZMod.val (d - c) ∧ ZMod.val (d - c) ≤ 4 * m) := by
      convert inS_cyclicNorm_iff m ( d - c ) ( by simpa [ sub_eq_zero ] using Ne.symm hcd.1 ) |>.1 _ using 1;
      convert hcd.2 using 1 ; rw [ show d - c = - ( c - d ) by ring, cyclicNorm_neg ];
    -- By the properties of the cyclic norm and the definition of adjacency in $G_m$, we know that $b$, $c$, and $d$ must satisfy certain conditions. Let's consider the differences $c - b$, $d - b$, and $d - c$.
    have h_diffs : (c.val + (6 * m + 1) - b.val) % (6 * m + 1) = (c - b).val ∧ (d.val + (6 * m + 1) - b.val) % (6 * m + 1) = (d - b).val ∧ (d.val + (6 * m + 1) - c.val) % (6 * m + 1) = (d - c).val := by
      haveI := Fact.mk ( by linarith : 1 < 6 * m + 1 ) ; simp +decide [ ← ZMod.val_natCast, Nat.cast_sub ( show b.val ≤ c.val + ( 6 * m + 1 ) from by linarith [ ZMod.val_lt b, ZMod.val_lt c ] ), Nat.cast_sub ( show b.val ≤ d.val + ( 6 * m + 1 ) from by linarith [ ZMod.val_lt b, ZMod.val_lt d ] ), Nat.cast_sub ( show c.val ≤ d.val + ( 6 * m + 1 ) from by linarith [ ZMod.val_lt c, ZMod.val_lt d ] ) ] ;
    -- Since $b$, $c$, and $d$ are distinct and their values are in the specified ranges, we can derive contradictions by considering the possible values of $c - b$, $d - b$, and $d - c$.
    have h_contradiction : (c.val + (6 * m + 1) - b.val) % (6 * m + 1) = c.val + (6 * m + 1) - b.val ∨ (c.val + (6 * m + 1) - b.val) % (6 * m + 1) = c.val - b.val := by
      by_cases h_case : c.val + (6 * m + 1) - b.val < 6 * m + 1;
      · exact Or.inl <| Nat.mod_eq_of_lt h_case;
      · rw [ Nat.mod_eq_sub_mod ];
        · rw [ Nat.mod_eq_of_lt ] <;> omega;
        · linarith
    have h_contradiction' : (d.val + (6 * m + 1) - b.val) % (6 * m + 1) = d.val + (6 * m + 1) - b.val ∨ (d.val + (6 * m + 1) - b.val) % (6 * m + 1) = d.val - b.val := by
      by_cases h_case : d.val + (6 * m + 1) - b.val < 6 * m + 1;
      · exact Or.inl <| Nat.mod_eq_of_lt h_case;
      · rw [ Nat.mod_eq_sub_mod ];
        · rw [ Nat.mod_eq_of_lt ] <;> omega;
        · linarith
    have h_contradiction'' : (d.val + (6 * m + 1) - c.val) % (6 * m + 1) = d.val + (6 * m + 1) - c.val ∨ (d.val + (6 * m + 1) - c.val) % (6 * m + 1) = d.val - c.val := by
      by_cases h_cases : d.val ≥ c.val;
      · rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ h_cases ];
        · rw [ Nat.sub_right_comm, Nat.add_sub_cancel ] ; norm_num [ Nat.mod_eq_of_lt ] ; omega;
        · omega;
      · rw [ Nat.mod_eq_of_lt ] <;> omega;
    omega

/-
PROBLEM
G_m is K₄-free.

PROVIDED SOLUTION
Unfold CliqueFree and IsNClique. For any finset t of size 4, show it's not a clique. Extract 4 elements from t using Finset.card_eq_four or similar. Apply no_four_clique to these 4 elements.

More concretely: CliqueFree 4 means ∀ t, ¬t.IsNClique 4. IsNClique means IsClique t ∧ t.card = 4. If we have a 4-clique, extract the 4 vertices and show they're pairwise adjacent, then apply no_four_clique.

Use SimpleGraph.CliqueFree and show by contradiction: if there exists a 4-clique {a,b,c,d}, then no_four_clique gives False.
-/
lemma cliqueFree_four (m : ℕ) (hm : m ≥ 2) : (G m).CliqueFree 4 := by
  intro t ht; simp_all +decide [ SimpleGraph.CliqueFree ] ;
  obtain ⟨ s, hs ⟩ := Finset.card_eq_succ.mp ht.2;
  obtain ⟨ u, hu, rfl, hu' ⟩ := hs; rw [ Finset.card_eq_three ] at hu'; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := hu'; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  exact no_four_clique m hm a b c s ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto ) ( by tauto )

/-
PROBLEM
Pigeonhole: no m+2 distinct elements in [0,2m] avoid all differences of m.

PROVIDED SOLUTION
We have m+2 distinct values in [0, 2m] with no two differing by m. Partition [0, 2m] into: C_0 = {0, m, 2m} (size 3, but at most 2 elements can be chosen: 0 and 2m, since m differs from both by m), and C_i = {i, i+m} for 1 ≤ i ≤ m-1 (each pair differs by m, so at most 1 from each). Total capacity = 2 + (m-1) = m+1 < m+2. By pigeonhole, impossible.

More concretely: define buckets b(x) = x % m for x ∈ [0, 2m]. There are m buckets (0 to m-1). Bucket 0 has elements {0, m, 2m}, other buckets {i, i+m}. The constraint f(i) + m ≠ f(j) means no two selected elements differ by exactly m. In bucket 0, at most 2 of {0, m, 2m} can be chosen (skip m or similar - actually we need to be careful: 0+m=m, m+m=2m, so if we pick 0 and 2m, that's fine since 0+m=m and 2m+m=3m≠0,2m in the sense that f(i)+m≠f(j), i.e., no f(i) and f(j) with f(i)+m = f(j)). Actually with pairs: if we pick both x and x+m, then f(i)+m = f(j) which is forbidden. So from {0,m,2m}, we can't pick both 0 and m (differ by m), and can't pick both m and 2m (differ by m), but can pick 0 and 2m (differ by 2m). So at most 2 from bucket 0. Each other bucket has 2 elements differing by m, so at most 1. Total: 2 + (m-1) = m+1 < m+2.

Use Finset.card_le_card_of_injOn or a direct pigeonhole argument. Actually, simplest approach: map each f(i) to f(i) % m, getting m+2 values in [0, m-1] (m buckets). By pigeonhole, two values f(i), f(j) fall in the same bucket, meaning f(i) ≡ f(j) mod m. Since both are in [0, 2m] and f(i) ≠ f(j), |f(i) - f(j)| = m or 2m. If |f(i)-f(j)| = m, then f(i)+m = f(j) or f(j)+m = f(i), contradicting hf_no_m. If |f(i)-f(j)| = 2m, then f(i) = 0 and f(j) = 2m (or vice versa). Now we still need another collision since m+2 > m+1. Actually wait, with m+2 pigeons and m holes, we get at least 2 collisions, or a hole with 3 pigeons. Let me think again...

Actually the cleanest way: define g : Fin (m+2) → Fin m by g(i) = f(i) % m. By pigeonhole (m+2 > m), there exist i ≠ j with g(i) = g(j). This means f(i) ≡ f(j) (mod m), so |f(i) - f(j)| ∈ {m, 2m} (since both in [0,2m] and distinct).

If |f(i) - f(j)| = m: WLOG f(j) = f(i) + m, contradicting hf_no_m.
If |f(i) - f(j)| = 2m: then {f(i), f(j)} = {0, 2m}. Now consider the remaining m elements (removing i and j from the m+2). They map to m values in [0, 2m] \ {0, 2m} = [1, 2m-1], each in [0, m-1] mod m. Actually we need another application of pigeonhole. The remaining m elements (indices other than i,j) have values in [0, 2m] \ {0, 2m} (by injectivity). These m values mod m give m values in {0, ..., m-1}. But the values 0 and 2m are excluded, so none of the remaining values are ≡ 0 mod m (since the only elements of [0,2m] that are ≡ 0 mod m are 0, m, 2m, and 0,2m are taken, so at most one remaining can be m). So the remaining m values mod m fall in {1, ..., m-1} ∪ {0 if value is m}. That's m buckets total. With m pigeons and m buckets, we could avoid collisions. But wait, let's check: bucket 0 can have at most value m (since 0 and 2m are taken). So bucket 0 has at most 1 element. Buckets 1 through m-1 each have at most 2 elements ({k, k+m} for k ∈ [1,m-1]). So total capacity is 1 + 2(m-1) = 2m-1 ≥ m for m ≥ 1. But our constraint says no two can have |difference| = m. So from each bucket {k, k+m}, at most 1. And bucket 0 has at most 1 (just m). So capacity is 1 + (m-1) = m. We have m remaining elements. So it's tight. But what about 0 and 2m? We have f(i) = 0 and f(j) = 2m. Constraint: f(i) + m ≠ f(k) for all k, i.e., no f(k) = m. And f(j) + m = 2m + m = 3m, and we need f(k) ≠ 3m, which is automatic since f(k) ≤ 2m. Also f(k) + m ≠ f(i) = 0, automatic since f(k) ≥ 0 so f(k)+m ≥ m > 0. And f(k) + m ≠ f(j) = 2m means f(k) ≠ m. So no remaining element equals m. So bucket 0 has 0 elements. The m remaining values fall in {1,...,m-1} ∪ {m+1,...,2m-1} = union of pairs {k, k+m} for k ∈ [1,m-1]. That's m-1 buckets. With m pigeons and m-1 buckets, by pigeonhole some bucket has 2 elements: f(a) and f(b) with |f(a)-f(b)| = m. Contradiction.

So the proof is: pigeonhole twice. First find i≠j with f(i) ≡ f(j) mod m. If difference is m, done. If difference is 2m (so {f(i),f(j)} = {0,2m}), then remaining m elements avoid m, so fall in m-1 buckets, and we find another collision with difference m.
-/
lemma pigeonhole_no_m_diff (m : ℕ) (hm : m ≥ 2)
    (f : Fin (m + 2) → ℕ) (hf_inj : Function.Injective f)
    (hf_range : ∀ i, f i ≤ 2 * m)
    (hf_no_m : ∀ i j, f i + m ≠ f j) : False := by
  -- By the pigeonhole principle, there exist indices $i \neq j$ such that $f(i) \equiv f(j) \pmod{m}$.
  obtain ⟨i, j, hij, hmod⟩ : ∃ i j : Fin (m + 2), i ≠ j ∧ f i % m = f j % m := by
    by_contra! h;
    exact absurd ( Finset.card_le_card ( show Finset.image ( fun i => f i % m ) Finset.univ ⊆ Finset.range m from Finset.image_subset_iff.mpr fun i _ => Finset.mem_range.mpr <| Nat.mod_lt _ <| by positivity ) ) ( by rw [ Finset.card_image_of_injective _ fun i j hij => not_imp_not.mp ( h i j ) hij ] ; simp +arith +decide );
  -- Since $f(i) \equiv f(j) \pmod{m}$, we have $|f(i) - f(j)| = km$ for some integer $k$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, |(f i : ℤ) - (f j : ℤ)| = k * m := by
    obtain ⟨ k, hk ⟩ := Nat.modEq_iff_dvd.mp hmod.symm;
    exact ⟨ Int.natAbs k, by simpa [ abs_mul, mul_comm ] using congr_arg abs hk ⟩;
  -- Since $|f(i) - f(j)| = km$ and $f(i), f(j) \in [0, 2m]$, we have $k \leq 2$.
  have hk_le_two : k ≤ 2 := by
    cases abs_cases ( f i - f j : ℤ ) <;> nlinarith [ hf_range i, hf_range j ];
  interval_cases k <;> simp_all +decide;
  · exact hij ( hf_inj ( by linarith ) );
  · cases abs_cases ( f i - f j : ℤ ) <;> [ exact hf_no_m j i ( by linarith ) ; exact hf_no_m i j ( by linarith ) ];
  · -- Consider the remaining $m$ elements $f(k)$ for $k \neq i, j$. They must be in the range $[1, 2m-1]$ and avoid $m$.
    have h_remaining : ∀ k : Fin (m + 2), k ≠ i ∧ k ≠ j → f k ∈ Finset.Icc 1 (2 * m - 1) ∧ f k ≠ m := by
      grind;
    -- By the pigeonhole principle, there exist indices $a \neq b$ such that $f(a) \equiv f(b) \pmod{m}$ among the remaining $m$ elements.
    obtain ⟨a, b, hab, hmod⟩ : ∃ a b : Fin (m + 2), a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧ f a % m = f b % m := by
      have h_pigeonhole : Finset.card (Finset.image (fun k => f k % m) (Finset.univ \ {i, j})) ≤ m - 1 := by
        have h_pigeonhole : Finset.image (fun k => f k % m) (Finset.univ \ {i, j}) ⊆ Finset.Icc 1 (m - 1) := by
          simp_all +decide [ Finset.subset_iff ];
          rintro x k hk₁ hk₂ rfl; specialize h_remaining k hk₁ hk₂; exact ⟨ Nat.pos_of_ne_zero fun h => by have := Nat.dvd_of_mod_eq_zero h; obtain ⟨ c, hc ⟩ := this; exact h_remaining.2 <| by nlinarith [ show c = 1 by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ 2 * m ) ] ], Nat.le_sub_one_of_lt <| Nat.mod_lt _ <| by linarith ⟩ ;
        exact le_trans ( Finset.card_le_card h_pigeonhole ) ( by simpa );
      contrapose! h_pigeonhole;
      rw [ Finset.card_image_of_injOn fun a ha b hb hab => by specialize h_pigeonhole a b; aesop ] ; simp +decide [ Finset.card_sdiff, * ];
      bv_omega;
    -- Since $f(a) \equiv f(b) \pmod{m}$, we have $|f(a) - f(b)| = km$ for some integer $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, |(f a : ℤ) - (f b : ℤ)| = k * m := by
      obtain ⟨ k, hk ⟩ := Nat.modEq_iff_dvd.mp hmod.2.2.2.2.symm;
      exact ⟨ Int.natAbs k, by simpa [ abs_mul, mul_comm ] using congr_arg abs hk ⟩;
    -- Since $|f(a) - f(b)| = km$ and $f(a), f(b) \in [1, 2m-1]$, we have $k \leq 1$.
    have hk_le_one : k ≤ 1 := by
      cases abs_cases ( ( f a : ℤ ) - f b ) <;> nlinarith [ Finset.mem_Icc.mp ( h_remaining a ⟨ hmod.1, hmod.2.1 ⟩ |>.1 ), Finset.mem_Icc.mp ( h_remaining b ⟨ hmod.2.2.1, hmod.2.2.2.1 ⟩ |>.1 ), Nat.sub_add_cancel ( by linarith : 1 ≤ 2 * m ) ];
    interval_cases k <;> simp_all +decide;
    · exact hab ( hf_inj ( by linarith ) );
    · grind +qlia

/-
PROVIDED SOLUTION
If u ≠ v and ¬G.Adj u v, then cyclicNorm(u-v) ∉ S (the connection set). Since u ≠ v, cyclicNorm(u-v) ≥ 1 (by cyclicNorm_eq_zero_iff). By cyclicNorm_le, cyclicNorm(u-v) ≤ (6m+1)/2 = 3m. So cyclicNorm(u-v) ∈ [1, 3m] \ S = [1, m-1] ∪ [m+1, 2m]. In particular, cyclicNorm(u-v) ≤ 2m.

Unfold G to see that ¬G.Adj u v means u = v ∨ ¬inS m (cyclicNorm ...). Since u ≠ v, we get ¬inS. Unfold inS: ¬(d = m ∨ (2m+1 ≤ d ∧ d ≤ 3m)), combined with d ≤ 3m (from cyclicNorm_le since (6m+1)/2 = 3m), gives d ≤ 2m.
-/
lemma not_adj_dist_le (m : ℕ) (hm : m ≥ 2) (u v : ZMod (6 * m + 1))
    (huv : u ≠ v) (hnadj : ¬(G m).Adj u v) :
    cyclicNorm (6 * m + 1) (u - v) ≤ 2 * m := by
  contrapose! hnadj;
  refine' ⟨ huv, Or.inr ⟨ by linarith, _ ⟩ ⟩;
  exact le_trans ( cyclicNorm_le _ ) ( by omega )

/-
PROVIDED SOLUTION
If u ≠ v and ¬G.Adj u v, then the cyclic norm is not in S. Since inS includes d = m, the cyclic norm cannot equal m. Unfold G to get ¬inS, then unfold inS to see d = m is excluded.
-/
lemma not_adj_dist_ne_m (m : ℕ) (hm : m ≥ 2) (u v : ZMod (6 * m + 1))
    (huv : u ≠ v) (hnadj : ¬(G m).Adj u v) :
    cyclicNorm (6 * m + 1) (u - v) ≠ m := by
  contrapose! hnadj;
  exact ⟨ huv, Or.inl hnadj ⟩

/-
PROBLEM
If all pairwise cyclic distances in s are ≤ 2m, there exists a base point v ∈ s
    such that all ZMod.val(x - v) ≤ 2m.

PROVIDED SOLUTION
Pick any v₀ ∈ s (s is nonempty since card = m+2 ≥ 4). For each x ∈ s with x ≠ v₀, cyclicNorm(x - v₀) ≤ 2m, so ZMod.val(x - v₀) ≤ 2m or ZMod.val(x - v₀) ≥ 4m+1 (since cyclicNorm = min(val, N-val) ≤ 2m with N = 6m+1).

Let B = {x ∈ s | x ≠ v₀ ∧ ZMod.val(x - v₀) > 2m}. These are elements with val(x - v₀) ≥ 4m+1.

If B = ∅, then v = v₀ works (for x = v₀, val(v₀ - v₀) = val(0) = 0 ≤ 2m).

If B ≠ ∅, let w be the element of B minimizing ZMod.val(w - v₀) (i.e., w has the smallest val among those ≥ 4m+1). Take v = w.

For x = w: val(w - w) = 0 ≤ 2m. ✓
For v₀: val(v₀ - w) = N - val(w - v₀) ≤ N - (4m+1) = 2m. ✓

For x ∈ s with x ≠ w, x ≠ v₀:
- If val(x - v₀) ≤ 2m (x was in A): val(x - w) = (val(x - v₀) + N - val(w - v₀)) mod N = val(x - v₀) + N - val(w - v₀) (since val(x-v₀) < val(w-v₀)). This is ≤ 2m + N - (4m+1) = 4m. Since cyclicNorm(x-w) ≤ 2m and val(x-w) ≤ 4m < 4m+1, we must have val(x-w) ≤ 2m. ✓

- If val(x - v₀) ≥ 4m+1 (x was in B): val(w - v₀) ≤ val(x - v₀) (w was minimal). So val(x - w) = val(x - v₀) - val(w - v₀) ≥ 0 and ≤ 6m - (4m+1) = 2m - 1 ≤ 2m. ✓

The formalization needs to be careful about the ZMod arithmetic. Use ZMod.val_sub for the subtraction formula.

Actually for the minimization, we can use Finset.min' on the image or use exists with suitable properties. A simpler approach: just pick w ∈ s maximizing ZMod.val(w - v₀) if B nonempty, and use v = w.

Actually no, we need the minimum in B, not maximum. Let me restate: w minimizes val(w - v₀) among B, so w has the smallest val(w - v₀) ≥ 4m+1.

For x ∈ B: val(x - v₀) ≥ val(w - v₀), so val(x - w) = val((x-v₀) - (w-v₀)). Since both vals are in [4m+1, 6m], and val(x-v₀) ≥ val(w-v₀), val(x-w) = val(x-v₀) - val(w-v₀). This uses the fact that for a, b in ZMod N with val(a) ≥ val(b) > 0, val(a-b) = val(a) - val(b) if val(a) - val(b) < N, which is true since both ≤ 6m gives difference ≤ 2m-1 < N.

For the formal proof, use the fact that ZMod.val (a - b) = (ZMod.val a - ZMod.val b) % N when val a ≥ val b, and since the result is < N, the mod is a no-op.
-/
lemma exists_base_point (m : ℕ) (hm : m ≥ 2)
    (s : Finset (ZMod (6 * m + 1))) (hs : s.card = m + 2)
    (h_le : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → cyclicNorm (6 * m + 1) (u - v) ≤ 2 * m) :
    ∃ v ∈ s, ∀ x ∈ s, ZMod.val (x - v) ≤ 2 * m := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ ∈ s, True := by
    exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hx, trivial ⟩;
  by_cases hB : ∃ w ∈ s, w ≠ v₀ ∧ (w - v₀).val ≥ 4 * m + 1;
  · -- Let $w$ be the element of $B$ minimizing $val(w - v₀)$.
    obtain ⟨w, hw₁, hw₂⟩ : ∃ w ∈ s, w ≠ v₀ ∧ (w - v₀).val ≥ 4 * m + 1 ∧ ∀ x ∈ s, x ≠ v₀ → (x - v₀).val ≥ 4 * m + 1 → (w - v₀).val ≤ (x - v₀).val := by
      have := Finset.exists_min_image ( s.filter fun x => x ≠ v₀ ∧ 4 * m + 1 ≤ ( x - v₀ ).val ) ( fun x => ( x - v₀ ).val ) ⟨ hB.choose, Finset.mem_filter.mpr ⟨ hB.choose_spec.1, hB.choose_spec.2.1, hB.choose_spec.2.2 ⟩ ⟩ ; aesop;
    use w;
    -- For any $x \in s$, if $x \neq w$ and $x \neq v₀$, then $(x - w).val \leq 2m$ by the properties of the cyclic norm and the minimality of $w$.
    have h_case2 : ∀ x ∈ s, x ≠ w → x ≠ v₀ → (x - w).val ≤ 2 * m := by
      intros x hx hxw hxv₀
      by_cases hxw_le : (x - v₀).val ≤ 2 * m;
      · have h_case2 : (x - w).val = (x - v₀).val + (6 * m + 1 - (w - v₀).val) := by
          have h_case2 : (x - w).val = ((x - v₀).val + (6 * m + 1 - (w - v₀).val)) % (6 * m + 1) := by
            haveI := Fact.mk ( by linarith : 1 < 6 * m + 1 ) ; simp +decide [ ← ZMod.val_natCast, Nat.cast_sub ( show ( w - v₀ ).val ≤ 6 * m + 1 from Nat.le_of_lt ( ZMod.val_lt _ ) ) ] ;
          rw [ h_case2, Nat.mod_eq_of_lt ];
          linarith [ Nat.sub_add_cancel ( show ( w - v₀ ).val ≤ 6 * m + 1 from by linarith [ ZMod.val_lt ( w - v₀ ) ] ) ];
        have := h_le x hx w hw₁ hxw; simp_all +decide [ cyclicNorm ] ;
        omega;
      · have h_case2 : (x - w).val = (x - v₀).val - (w - v₀).val := by
          have h_case2 : (x - w).val = ((x - v₀).val - (w - v₀).val) % (6 * m + 1) := by
            have h_case2 : (x - w).val = ((x - v₀).val - (w - v₀).val) % (6 * m + 1) := by
              have h_case2 : (x - w) = (x - v₀) - (w - v₀) := by
                ring
              rw [ h_case2, ZMod.val_sub ];
              · rw [ Nat.mod_eq_of_lt ];
                exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( by linarith [ ZMod.val_lt ( x - v₀ ), ZMod.val_lt ( w - v₀ ) ] );
              · contrapose! hw₂;
                exact fun _ _ => ⟨ x, hx, hxv₀, by linarith [ show ( x - v₀ ).val ≥ 4 * m + 1 from by have := h_le x hx v₀ hv₀.1 hxv₀; unfold cyclicNorm at this; omega ], hw₂ ⟩;
            exact h_case2;
          rw [ h_case2, Nat.mod_eq_of_lt ];
          exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( by linarith [ ZMod.val_lt ( x - v₀ ), ZMod.val_lt ( w - v₀ ) ] );
        have := h_le x hx w hw₁ hxw;
        unfold cyclicNorm at this;
        simp_all +decide [ min_le_iff ];
        contrapose! this;
        exact ⟨ this, by linarith [ Nat.sub_add_cancel ( by linarith : ( w - v₀ ).val ≤ ( x - v₀ ).val ), show ( x - v₀ ).val ≤ 6 * m from Nat.le_of_lt_succ ( by linarith [ ZMod.val_lt ( x - v₀ ) ] ) ] ⟩;
    refine' ⟨ hw₁, fun x hx => _ ⟩ ; by_cases hx' : x = w <;> by_cases hx'' : x = v₀ <;> simp_all +decide [ ZMod.val_sub ] ;
    rw [ show v₀ - w = - ( w - v₀ ) by ring, ZMod.neg_val ];
    split_ifs <;> omega;
  · refine' ⟨ v₀, hv₀.1, fun x hx => _ ⟩ ; by_cases hx' : x = v₀ <;> simp_all +decide [ cyclicNorm ];
    cases h_le x hx v₀ hv₀ hx' <;> linarith [ hB x hx hx' ]

/-
PROBLEM
When two ZMod values both have val ≤ 2m (relative to same base), their
    difference's cyclicNorm equals the integer absolute difference.

PROVIDED SOLUTION
We have N = 6m+1, val(a) ≤ 2m, val(b) ≤ 2m, a ≠ b.

cyclicNorm(a-b) = min(val(a-b), N - val(a-b)).

Case 1: val(a) ≥ val(b). Then val(a-b) = val(a) - val(b) (since val(a) - val(b) ∈ [0, 2m] ⊂ [0, N-1], so (val(a) - val(b)) % N = val(a) - val(b)).
The integer |val(a) - val(b)| = val(a) - val(b) ∈ [0, 2m].
N - val(a-b) = N - (val(a) - val(b)) ≥ N - 2m = 4m+1 > 2m.
So min = val(a) - val(b) = Int.natAbs(val(a) - val(b)). ✓

Case 2: val(a) < val(b). Then val(a-b) = val(a) + N - val(b) (since val(a) - val(b) < 0, (val(a) - val(b)) % N = val(a) - val(b) + N).
val(a-b) = val(a) + N - val(b) = val(a) + 6m+1 - val(b) ≥ 6m+1 - 2m = 4m+1.
N - val(a-b) = val(b) - val(a) ∈ [1, 2m].
So min = N - val(a-b) = val(b) - val(a) = Int.natAbs(val(a) - val(b)). ✓

In both cases, cyclicNorm = |val(a) - val(b)| = Int.natAbs((val(a) : ℤ) - val(b)).

Use ZMod.val_sub or direct computation with ZMod.val for the subtraction.
-/
lemma cyclicNorm_of_small_vals (m : ℕ) (hm : m ≥ 2)
    (a b : ZMod (6 * m + 1)) (ha : ZMod.val a ≤ 2 * m) (hb : ZMod.val b ≤ 2 * m)
    (hab : a ≠ b) :
    cyclicNorm (6 * m + 1) (a - b) = Int.natAbs ((ZMod.val a : ℤ) - ZMod.val b) := by
  -- By definition of cyclicNorm, we have cyclicNorm (6 * m + 1) (a - b) = min (a.val - b.val) (6 * m + 1 - (a.val - b.val)) if a.val > b.val, and cyclicNorm (6 * m + 1) (a - b) = min (6 * m + 1 - (a.val - b.val)) (a.val - b.val) if a.val < b.val.
  simp [cyclicNorm];
  -- By definition of subtraction in ZMod, we have $(a - b).val = (a.val + (6 * m + 1 - b.val)) % (6 * m + 1)$.
  have h_sub_val : (a - b).val = if a.val ≥ b.val then a.val - b.val else 6 * m + 1 + a.val - b.val := by
    split_ifs <;> simp_all +decide [ ZMod.val_sub ];
    rw [ show ( a - b : ZMod ( 6 * m + 1 ) ) = ( a.val + ( 6 * m + 1 - b.val ) ) from ?_, ZMod.val_add ];
    · norm_cast;
      rw [ Int.subNatNat_of_le ] <;> norm_cast <;> try linarith;
      rw [ Nat.mod_eq_of_lt ] <;> norm_num;
      · rw [ Nat.mod_eq_of_lt ] <;> omega;
      · rw [ Nat.mod_eq_of_lt ] <;> omega;
    · haveI := Fact.mk ( by linarith : 1 < 6 * m + 1 ) ; norm_num [ sub_eq_add_neg ] ;
      norm_cast;
      erw [ ZMod.natCast_self ];
  split_ifs at h_sub_val <;> simp_all +decide [ ZMod.cast, ZMod.val ];
  · rw [ min_eq_left ] <;> omega;
  · rw [ min_eq_right ] <;> omega

/-
PROVIDED SOLUTION
Use exists_base_point to get v ∈ s with ∀ x ∈ s, ZMod.val(x - v) ≤ 2m.

Use s.equivFin or Fintype.equivOfCardEq to get an enumeration e : Fin(m+2) ≃ s (since s.card = m+2).

Define f : Fin(m+2) → ℕ by f(i) = ZMod.val(e(i) - v).

Prove:
1. f is injective: If f(i) = f(j), then ZMod.val(e(i) - v) = ZMod.val(e(j) - v), so e(i) - v = e(j) - v (by ZMod.val_injective), so e(i) = e(j), so i = j (by e.injective).

2. ∀ i, f(i) ≤ 2m: By the base point property.

3. ∀ i j, f(i) + m ≠ f(j): Suppose f(i) + m = f(j). Then val(e(j) - v) - val(e(i) - v) = m as integers. Both vals are ≤ 2m. By cyclicNorm_of_small_vals, cyclicNorm(e(j) - e(i)) = Int.natAbs(val(e(j)-v) - val(e(i)-v)). Wait, we need cyclicNorm((e(j)-v) - (e(i)-v)) = Int.natAbs(val(e(j)-v) - val(e(i)-v)). Note (e(j)-v) - (e(i)-v) = e(j) - e(i). Since val(e(j)-v) ≤ 2m and val(e(i)-v) ≤ 2m, by cyclicNorm_of_small_vals, cyclicNorm(e(j) - e(i)) = |val(e(j)-v) - val(e(i)-v)| = |f(j) - f(i)| = m. But h_ne says cyclicNorm(e(j) - e(i)) ≠ m for e(j) ≠ e(i). And e(j) ≠ e(i) because f(j) = f(i) + m > f(i) (since m ≥ 2) so f(j) ≠ f(i) so e(j) - v ≠ e(i) - v so e(j) ≠ e(i). Contradiction.
-/
set_option maxHeartbeats 1600000 in
lemma lift_indep_to_nat (m : ℕ) (hm : m ≥ 2)
    (s : Finset (ZMod (6 * m + 1))) (hs : s.card = m + 2)
    (h_le : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → cyclicNorm (6 * m + 1) (u - v) ≤ 2 * m)
    (h_ne : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → cyclicNorm (6 * m + 1) (u - v) ≠ m) :
    ∃ f : Fin (m + 2) → ℕ, Function.Injective f ∧
      (∀ i, f i ≤ 2 * m) ∧ (∀ i j, f i + m ≠ f j) := by
  obtain ⟨ v, hv, hv' ⟩ := exists_base_point m hm s hs h_le;
  -- Use s.equivFin to get an enumeration e : Fin(m+2) ≃ s.
  obtain ⟨e, he⟩ : ∃ e : Fin (m + 2) ≃ s, True := by
    exact ⟨ Fintype.equivOfCardEq ( by aesop ), trivial ⟩;
  refine' ⟨ fun i => ( e i : ZMod ( 6 * m + 1 ) ) - v |> ZMod.val, _, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
  · intro i j hij; have := ZMod.val_injective ( 6 * m + 1 ) hij; aesop;
  · intro i j hij; specialize h_ne ( e i ) ( e i |>.2 ) ( e j ) ( e j |>.2 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    -- By definition of $f$, we know that $cyclicNorm (e i - e j) = |f i - f j|$.
    have h_cyclicNorm : cyclicNorm (6 * m + 1) ((e i : ZMod (6 * m + 1)) - (e j : ZMod (6 * m + 1))) = Int.natAbs ((e i - v).val - (e j - v).val) := by
      convert cyclicNorm_of_small_vals m hm ( e i - v ) ( e j - v ) _ _ _ using 1 <;> norm_num [ hv' ];
      rintro rfl; linarith [ show m > 0 by linarith ] ;
    exact h_ne ( by rintro rfl; linarith ) ( by omega )

/-
PROBLEM
G_m has no independent set of size m+2.

PROVIDED SOLUTION
We need (G m)ᶜ.CliqueFree (m + 2), i.e., no set of m+2 vertices are pairwise adjacent in the complement, i.e., pairwise non-adjacent in G (forming an independent set of size m+2).

Suppose for contradiction there exists a clique of size m+2 in (G m)ᶜ. Let s be this clique as a Finset. Then for all u, v ∈ s with u ≠ v, (G m)ᶜ.Adj u v, which means u ≠ v ∧ ¬(G m).Adj u v.

By not_adj_dist_le, for all u ≠ v in s: cyclicNorm(u - v) ≤ 2m.
By not_adj_dist_ne_m, for all u ≠ v in s: cyclicNorm(u - v) ≠ m.

By lift_indep_to_nat, there exists f : Fin(m+2) → ℕ with f injective, f(i) ≤ 2m, and f(i) + m ≠ f(j).

By pigeonhole_no_m_diff, this is impossible. Contradiction.
-/
lemma indepFree (m : ℕ) (hm : m ≥ 2) : (G m)ᶜ.CliqueFree (m + 2) := by
  intro T hT;
  -- Apply the lift_indep_to_nat lemma to obtain the existence of such a function f.
  obtain ⟨f, hf_inj, hf_range, hf_no_m⟩ := lift_indep_to_nat m hm T (by
  exact hT.2) (by
  intro u hu v hv huv; exact not_adj_dist_le m hm u v huv (by
  exact hT.1 hu hv huv |> fun h => by simpa [ huv ] using h;)) (by
  intros u hu v hv huv h_eq_m
  have h_adj : (G m).Adj u v := by
    exact ⟨ huv, Or.inl h_eq_m ⟩;
  have := hT.1 hu hv; aesop;);
  exact?

end DoublySaturated