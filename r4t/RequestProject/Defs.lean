import Mathlib

namespace DoublySaturated

/-! # Definitions for Doubly Saturated Ramsey Graphs

We define R(s,t) graphs and doubly saturated R(s,t) graphs,
then define the circulant graph family and prove basic properties.
-/

section RamseyDefs

variable {V : Type*}

/-- A graph G is R(s,t) if it has no clique of size s and no independent set of size t. -/
def IsRST (G : SimpleGraph V) (s t : ℕ) : Prop :=
  G.CliqueFree s ∧ Gᶜ.CliqueFree t

/-- A graph G is doubly saturated R(s,t) if it is R(s,t), but adding any non-edge
    results in a graph that is no longer R(s,t), and removing any edge results in
    a graph that is no longer R(s,t). -/
def IsDoublySaturatedRST (G : SimpleGraph V) (s t : ℕ) : Prop :=
  IsRST G s t ∧
  (∀ u v : V, u ≠ v → ¬G.Adj u v →
    ¬IsRST (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) s t) ∧
  (∀ u v : V, G.Adj u v →
    ¬IsRST (G \ SimpleGraph.fromEdgeSet {s(u, v)}) s t)

end RamseyDefs

section CyclicNorm

variable {n : ℕ} [NeZero n]

/-- The cyclic norm: shortest distance to 0 in ℤ/nℤ. -/
def cyclicNorm (n : ℕ) [NeZero n] (x : ZMod n) : ℕ :=
  min (ZMod.val x) (n - ZMod.val x)

/-
PROVIDED SOLUTION
Use ZMod.neg_val' to get (-x).val = (n - x.val) % n. When x.val = 0, both sides are 0. When x.val > 0, (-x).val = n - x.val, so min(n - x.val, n - (n - x.val)) = min(n - x.val, x.val) = min(x.val, n - x.val).
-/
lemma cyclicNorm_neg (x : ZMod n) :
    cyclicNorm n (-x) = cyclicNorm n x := by
  unfold cyclicNorm;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ ZMod.neg_val' ];
  · fin_cases x ; trivial;
  · rcases x with ⟨ _ | x, hx ⟩ <;> norm_num [ Nat.mod_eq_of_lt ] at *;
    erw [ Nat.mod_eq_of_lt ] <;> norm_num [ ZMod.val ] ; omega

lemma cyclicNorm_zero : cyclicNorm n (0 : ZMod n) = 0 := by
  simp [cyclicNorm, ZMod.val_zero]

/-
PROVIDED SOLUTION
cyclicNorm n x = min(x.val, n - x.val). Since x.val < n, we have n - x.val ≥ 0. If x.val ≤ n/2, then cyclicNorm = x.val ≤ n/2. If x.val > n/2, then cyclicNorm = n - x.val < n/2 ≤ n/2.
-/
lemma cyclicNorm_le (x : ZMod n) : cyclicNorm n x ≤ n / 2 := by
  -- By definition of cyclic norm, we know that for any x in ZMod n, either x.val ≤ n/2 or (n - x.val) ≤ n/2.
  have h_cases : ∀ x : ZMod n, x.val ≤ n / 2 ∨ (n - x.val) ≤ n / 2 := by
    grind +ring;
  unfold cyclicNorm; aesop;

/-
PROVIDED SOLUTION
Forward: if cyclicNorm = 0, then min(x.val, n - x.val) = 0, so x.val = 0, so x = 0 (by ZMod.val_eq_zero or similar). Backward: if x = 0, trivial by cyclicNorm_zero.
-/
lemma cyclicNorm_eq_zero_iff (x : ZMod n) : cyclicNorm n x = 0 ↔ x = 0 := by
  by_cases h : x = 0 <;> simp +decide [ h, cyclicNorm ];
  exact Nat.sub_ne_zero_of_lt ( ZMod.val_lt x )

end CyclicNorm

section Graph

instance (m : ℕ) : NeZero (6 * m + 1) := ⟨by omega⟩

/-- The connection set S = {m} ∪ [2m+1, 3m].
    A cyclic distance d is in S iff d = m or 2m+1 ≤ d ≤ 3m. -/
def inS (m d : ℕ) : Prop :=
  d = m ∨ (2 * m + 1 ≤ d ∧ d ≤ 3 * m)

instance (m d : ℕ) : Decidable (inS m d) := by
  unfold inS; infer_instance

/-- The complement of the connection set: distances [1, m-1] ∪ [m+1, 2m].
    Equivalently, 0 < d ≤ 2m and d ≠ m. -/
def inSc (m d : ℕ) : Prop :=
  (1 ≤ d ∧ d ≤ m - 1) ∨ (m + 1 ≤ d ∧ d ≤ 2 * m)

instance (m d : ℕ) : Decidable (inSc m d) := by
  unfold inSc; infer_instance

/-- The circulant graph G_m on ℤ/(6m+1)ℤ with connection set {m} ∪ [2m+1, 3m].
    Two vertices u, v are adjacent iff their cyclic distance is in the connection set. -/
def G (m : ℕ) : SimpleGraph (ZMod (6 * m + 1)) where
  Adj u v := u ≠ v ∧ inS m (cyclicNorm (6 * m + 1) (u - v))
  symm u v := by
    intro ⟨hne, hs⟩
    refine ⟨hne.symm, ?_⟩
    have : v - u = -(u - v) := by ring
    rw [this, cyclicNorm_neg]
    exact hs
  loopless := ⟨fun v ⟨h, _⟩ => h rfl⟩

/-- The adjacency of the circulant graph G_m is decidable. -/
instance (m : ℕ) : DecidableRel (G m).Adj := by
  intro u v
  unfold G
  exact inferInstance

/-- The graph G_m is translation-invariant: Adj u v ↔ Adj (u+w) (v+w). -/
lemma G_adj_translate (m : ℕ) (u v w : ZMod (6 * m + 1)) :
    (G m).Adj u v ↔ (G m).Adj (u + w) (v + w) := by
  unfold G
  constructor <;> intro ⟨hne, hs⟩
  · constructor
    · intro h; exact hne (add_right_cancel h)
    · rwa [show (u + w) - (v + w) = u - v from by ring]
  · constructor
    · intro h; exact hne (by rw [h])
    · rwa [show u - v = (u + w) - (v + w) from by ring]

/-- Adjacency in G_m only depends on the difference u - v. -/
lemma G_adj_sub (m : ℕ) (u v : ZMod (6 * m + 1)) :
    (G m).Adj u v ↔ (G m).Adj (u - v) 0 := by
  have h := G_adj_translate m u v (-v)
  simp only [add_neg_cancel] at h
  rw [h]
  ring_nf

/-
PROBLEM
Characterization of inS in terms of the directed edge set D.
    cyclicNorm ∈ S iff val ∈ D = {m, 5m+1} ∪ [2m+1, 4m].

PROVIDED SOLUTION
Unfold inS and cyclicNorm. We have cyclicNorm = min(val(x), (6m+1) - val(x)).
Since x ≠ 0, val(x) ∈ [1, 6m]. The cyclic norm is in S = {m} ∪ [2m+1, 3m] iff:
Either min(val(x), N-val(x)) = m, which means val(x) = m or N - val(x) = m (i.e. val(x) = 5m+1).
Or 2m+1 ≤ min(val(x), N-val(x)) ≤ 3m, which means both val(x) ≥ 2m+1 and N-val(x) ≥ 2m+1 (i.e. val(x) ≤ 4m),
and at least one of val(x) ≤ 3m or N-val(x) ≤ 3m. Since both ≥ 2m+1 and ≤ 4m, min is in [2m+1, 3m] iff val(x) ∈ [2m+1, 4m].
So the condition is: val(x) = m ∨ val(x) = 5m+1 ∨ (2m+1 ≤ val(x) ≤ 4m).
-/
lemma inS_cyclicNorm_iff (m : ℕ) (x : ZMod (6 * m + 1)) (hx : x ≠ 0) :
    inS m (cyclicNorm (6 * m + 1) x) ↔
      (ZMod.val x = m ∨ ZMod.val x = 5 * m + 1 ∨
       (2 * m + 1 ≤ ZMod.val x ∧ ZMod.val x ≤ 4 * m)) := by
  unfold cyclicNorm;
  cases min_cases x.val ( 6 * m + 1 - x.val ) <;> simp_all +decide [ inS ];
  · omega;
  · have := ZMod.val_lt x; omega;

end Graph

end DoublySaturated