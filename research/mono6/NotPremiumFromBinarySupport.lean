import PEqualNP.Defs

/-!
Generic no-NOT-advantage criterion from essential-input counting.

The build/live compression and free-complement compilation architecture is
adapted from the proof of L-meta-13647 in PR17808:
https://github.com/open-goat/pequalnp-proofs/pull/17808
The source was audited locally as positive13647-pr17808.lean. The signal type
is generalized here from fixed bit vectors to arbitrary Boolean functions;
no finite truth-table search is used in this file.
-/

namespace PEqualNP.Research.NotPremiumFromBinarySupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

end Live

abbrev Signal (α : Type) := α → Bool

noncomputable section
local instance (priority := 2000) signalDecEq {α : Type} : DecidableEq (Signal α) := Classical.decEq _

section Signals

variable {α : Type}

def zero : Signal α := fun _ => false
def one : Signal α := fun _ => true
def neg (a : Signal α) : Signal α := fun x => !(a x)
def conj (a b : Signal α) : Signal α := fun x => a x && b x
def disj (a b : Signal α) : Signal α := fun x => a x || b x
def basicOps (a b : Signal α) : Finset (Signal α) :=
  {conj a b, disj a b, conj a (neg b), conj b (neg a)}

@[simp] theorem neg_zero : neg (zero : Signal α) = one := rfl
@[simp] theorem neg_one : neg (one : Signal α) = zero := rfl
@[simp] theorem neg_neg (a : Signal α) : neg (neg a) = a := by
  funext x; simp [neg]
@[simp] theorem conj_zero (a : Signal α) : conj a zero = zero := by
  funext x; simp [conj, zero]
@[simp] theorem zero_conj (a : Signal α) : conj zero a = zero := by
  funext x; simp [conj, zero]
@[simp] theorem conj_one (a : Signal α) : conj a one = a := by
  funext x; simp [conj, one]
@[simp] theorem one_conj (a : Signal α) : conj one a = a := by
  funext x; simp [conj, one]
@[simp] theorem conj_self (a : Signal α) : conj a a = a := by
  funext x; simp [conj]
@[simp] theorem conj_neg (a : Signal α) : conj a (neg a) = zero := by
  funext x; simp [conj, neg, zero]
@[simp] theorem neg_conj (a : Signal α) : conj (neg a) a = zero := by
  funext x; simp [conj, neg, zero]
@[simp] theorem disj_zero (a : Signal α) : disj a zero = a := by
  funext x; simp [disj, zero]
theorem conj_comm (a b : Signal α) : conj a b = conj b a := by
  funext x; simp [conj, Bool.and_comm]
theorem neg_disj (a b : Signal α) : neg (disj a b) = conj (neg a) (neg b) := by
  funext x; simp [conj, disj, neg]
theorem neg_conj_eq (a b : Signal α) : neg (conj a b) = disj (neg a) (neg b) := by
  funext x; simp [conj, disj, neg]

def holds (av : Finset (Signal α)) (z : Signal α) : Prop :=
  z = zero ∨ z = one ∨ ∃ a ∈ av, z = a ∨ z = neg a

theorem holds_insert {av : Finset (Signal α)} {z a : Signal α} (h : holds av z) :
    holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset (Signal α)} {z : Signal α} (h : holds av z) :
    holds av (neg z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl neg_zero)
  · exact .inl neg_one
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl (neg_neg a)⟩)

def reachable (av : Finset (Signal α)) (z : Signal α) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧
    ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset (Signal α)} {z : Signal α} (h : reachable av z) :
    reachable av (neg z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem and_reach {av : Finset (Signal α)} {x y : Signal α}
    (hx : holds av x) (hy : holds av y) : reachable av (conj x y) := by
  have const : holds av (zero : Signal α) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [zero_conj]; exact .inl const
  · rw [one_conj]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [conj_zero]; exact .inl const
  · rw [conj_one]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [conj_self, conj_neg, neg_conj]
    · exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩))
    · exact .inl const
    · exact .inl const
    · exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : Signal α) (hw : w ∈ basicOps a b) (z : Signal α)
      (hz : z = w ∨ z = neg w) : reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw,
      .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps]) _ (.inl rfl)
  · exact add _ (by simp [basicOps]) _ (.inl rfl)
  · exact add _ (by simp [basicOps] : conj b (neg a) ∈ basicOps a b) _
      (.inl (conj_comm ..))
  · exact add _ (by simp [basicOps] : disj a b ∈ basicOps a b) _
      (.inr (neg_disj ..).symm)

theorem or_reach {av : Finset (Signal α)} {x y : Signal α}
    (hx : holds av x) (hy : holds av y) : reachable av (disj x y) := by
  simpa only [neg_conj_eq, neg_neg] using
    reachable_not (and_reach (holds_not hx) (holds_not hy))

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_apply (w : List (Signal α)) (i : ℕ) (x : α) :
    (w.map (fun z => z x)).getD i false = (w.getD i zero) x := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), zero]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List (Signal α)) (g : Gate) : Signal α := match g.op with
  | .not => neg ((g.inputs.head?.map (fun i => w.getD i zero)).getD zero)
  | .and => (g.inputs.map fun i => w.getD i zero).foldr conj one
  | .or => (g.inputs.map fun i => w.getD i zero).foldr disj zero
  | _ => zero

theorem action_spec (w : List (Signal α)) (g : Gate) (hg : legal g) (x : α) :
    step (w.map (fun z => z x)) g = (w ++ [action w g]).map (fun z => z x) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_apply, List.map_append] <;>
    simp [action, GateOp.eval, conj, disj, neg, zero, one]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset (Signal α)} {w : List (Signal α)}
    (hw : ∀ u ∈ w, holds av u) (i : ℕ) : holds av (w.getD i zero) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

theorem gate_reach (w : List (Signal α)) (av : Finset (Signal α))
    (hw : ∀ u ∈ w, holds av u) (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
      action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons,
      List.foldr_nil, List.foldr_cons, Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some, disj_zero, conj_one, neg_zero]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (Signal α)) (av : Finset (Signal α)) (hw : ∀ u ∈ w, holds av u)
    (f : Signal α) (hnc : f ≠ zero ∧ f ≠ one)
    (he : ∀ x, (gs.foldl step (w.map (fun z => z x))).getD out false = f x) :
    ∃ t, (t = f ∨ t = neg f) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out zero = f := by
      funext x
      simpa only [List.foldl_nil, read_apply] using he x
    have h := hv ▸ available_read hw out
    rcases h with hz | ho | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnc.1 hz)
    · exact False.elim (hnc.2 ho)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa using congrArg neg eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ x, (gs.foldl step ((w ++ [z]).map (fun v => v x))).getD out false = f x := by
      intro x; simpa only [List.foldl_cons, stepOK] using he x
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (Signal α)) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases isNot : isBinary g
    · simp only [isNot, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, isNot] using cont av hw stepClass
    · simp only [isNot, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, isNot]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

theorem ops_separate (x y : α) (a b : Signal α) (z : Signal α)
    (hz : z ∈ basicOps a b) (hd : z x ≠ z y) : a x ≠ a y ∨ b x ≠ b y := by
  by_contra! h
  apply hd
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [conj, disj, neg, h.1, h.2]

end Signals

/-- Every input can change the output when that one input is flipped. -/
def AllEssential {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!(x i)))

def input {n : ℕ} (i : Fin n) : Signal (Fin n → Bool) := fun x => x i

theorem input_injective {n : ℕ} : Function.Injective (input (n := n)) := by
  intro i j h
  have he := congrFun h (fun k => decide (k = i))
  have hj : j = i := by simpa [input] using he.symm
  exact hj.symm

/-- A circuit computing an essential n-input function uses at least n-1
    AND/OR gates, even if complements are free. -/
theorem essential_binary_bound {n : ℕ} (f : (Fin n → Bool) → Bool)
    (essential : AllEssential f) (C : Circuit) (fit : FanInTwo C)
    (computes : ∀ x, C.eval (List.ofFn x) = f x) :
    n ≤ binaryCost C.gates + 1 := by
  classical
  by_cases hn : n = 0
  · omega
  have nonconstant : f ≠ zero ∧ f ≠ one := by
    obtain ⟨x, hx⟩ := essential ⟨0, by omega⟩
    constructor <;> intro he <;> apply hx <;> simp [he, zero, one]
  let inputs := List.ofFn (input (n := n))
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (x : Fin n → Bool) :
      (C.gates.foldl step (inputs.map (fun z => z x))).getD C.output false = f x := by
    have same : inputs.map (fun z => z x) = List.ofFn x := by
      dsimp [inputs]
      rw [List.map_ofFn]
      rfl
    rw [same]
    exact computes x
  obtain ⟨t, ht, run⟩ := compile C.gates C.output fit inputs inputs.toFinset init f nonconstant evaluate
  obtain ⟨s, hs, hlive⟩ := compress run
  have all : inputs.toFinset ⊆ s := by
    intro u hu
    obtain ⟨i, rfl⟩ : ∃ i : Fin n, input i = u := by
      simpa [inputs] using hu
    obtain ⟨x, hx⟩ := essential i
    let y := Function.update x i (!(x i))
    have htxy : t x ≠ t y := by
      rcases ht with rfl | rfl
      · exact hx
      · simpa [neg] using hx
    obtain ⟨w, hw, hsep⟩ := live_separates (fun z => z x ≠ z y) htxy (ops_separate x y) hlive
    obtain ⟨j, hj⟩ : ∃ j : Fin n, input j = w := by
      simpa [inputs] using hs hw
    have he : j = i := by
      by_contra hne
      apply hsep
      simp [← hj, input, y, hne]
    subst j
    exact hj.symm ▸ hw
  have card := live_card hlive
  have initial_card : inputs.toFinset.card = n := by
    rw [List.toFinset_card_of_nodup]
    · simp [inputs]
    · exact List.nodup_ofFn.mpr input_injective
  have lower := Finset.card_le_card all
  omega

/-- If an essential n-input function has an AND/OR implementation of size at
    most n, NOT gates cannot improve its optimal circuit size. -/
theorem transfer_of_ao_size_le_inputs {n : ℕ} (f : (Fin n → Bool) → Bool)
    (essential : AllEssential f) (W : Circuit) (mono : Monotone2 W)
    (small : W.size ≤ n) (correct : ∀ x, W.eval (List.ofFn x) = f x)
    (s : ℕ) (hs : HasCircuitSize n f s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x, D.eval (List.ofFn x) = f x := by
  obtain ⟨C, fit, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := essential_binary_bound f essential C fit computes
    exact ⟨W, mono, by omega, correct⟩
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fit g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr
      (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end
end PEqualNP.Research.NotPremiumFromBinarySupport
