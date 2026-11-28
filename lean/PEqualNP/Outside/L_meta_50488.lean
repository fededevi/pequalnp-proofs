import Mathlib
import PEqualNP.Defs

def PEqualNP.Outside.L_meta_50488.cands (S : List ℕ) : List ℕ :=
  ((S.flatMap fun a => S.flatMap fun b => [a &&& b, a ||| b]).filter fun c => !S.contains c).dedup

def PEqualNP.Outside.L_meta_50488.ncands (m : ℕ) (S : List ℕ) : List ℕ :=
  (S.map fun a => m ^^^ a).filter fun c => !S.contains c

def PEqualNP.Outside.L_meta_50488.reach (m : ℕ) (outs : List ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, S => outs.all fun o => S.contains o
  | G + 1, k, S =>
    (outs.all fun o => S.contains o) ||
      (decide ((outs.filter fun o => !S.contains o).length ≤ G + 1) &&
        ((PEqualNP.Outside.L_meta_50488.cands S).any
            (fun c => PEqualNP.Outside.L_meta_50488.reach m outs G k (c :: S)) ||
          (decide (0 < k) && (PEqualNP.Outside.L_meta_50488.ncands m S).any
            (fun c => PEqualNP.Outside.L_meta_50488.reach m outs G (k - 1) (c :: S)))))

theorem PEqualNP.Outside.L_meta_50488.miss_zero (outs S : List ℕ)
    (h : (outs.all fun o => S.contains o) = true) :
    (outs.filter fun o => !S.contains o).length = 0 := by
  rw [List.all_eq_true] at h
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro o ho
  have := h o ho
  simpa using this

theorem PEqualNP.Outside.L_meta_50488.reach_miss (m : ℕ) (outs : List ℕ) (G k : ℕ) (S : List ℕ)
    (h : PEqualNP.Outside.L_meta_50488.reach m outs G k S = true) :
    (outs.filter fun o => !S.contains o).length ≤ G := by
  cases G with
  | zero =>
    simp only [PEqualNP.Outside.L_meta_50488.reach] at h
    rw [PEqualNP.Outside.L_meta_50488.miss_zero outs S h]
  | succ G =>
    simp only [PEqualNP.Outside.L_meta_50488.reach, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · rw [PEqualNP.Outside.L_meta_50488.miss_zero outs S h]; omega
    · exact h.1

theorem PEqualNP.Outside.L_meta_50488.miss_cons (outs : List ℕ) (hnd : outs.Nodup) (c : ℕ)
    (S : List ℕ) :
    (outs.filter fun o => !S.contains o).length ≤
      (outs.filter fun o => !(c :: S).contains o).length + 1 := by
  have h1 : (outs.filter fun o => !(c :: S).contains o) =
      (outs.filter fun o => !S.contains o).erase c := by
    rw [(hnd.filter _).erase_eq_filter, List.filter_filter]
    apply List.filter_congr
    intro o _
    by_cases h : o = c <;> simp [h]
  rw [h1, List.length_erase]
  split <;> omega

theorem PEqualNP.Outside.L_meta_50488.getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h2 : ¬ i = w.length := by omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [h2]

theorem PEqualNP.Outside.L_meta_50488.gate (T : ℕ) (W : ℕ → List Bool) (S : List ℕ)
    (h0 : 0 ∈ S) (hm : 2 ^ T - 1 ∈ S)
    (hinv : ∀ i, ∃ c ∈ S, c < 2 ^ T ∧ ∀ t < T, c.testBit t = (W t).getD i false)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hg : (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∃ c, (c < 2 ^ T ∧ ∀ t < T, c.testBit t =
        g.op.eval (g.inputs.map fun i => (W t).getD i false)) ∧
      (c ∈ S ∨
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a ∈ S, ∃ b ∈ S, c = a &&& b ∨ c = a ||| b) ∨
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ a ∈ S, c = (2 ^ T - 1) ^^^ a)) := by
  have hpos : 0 < 2 ^ T := Nat.two_pow_pos T
  have hmlt : 2 ^ T - 1 < 2 ^ T := by omega
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, r⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨2 ^ T - 1, ⟨hmlt, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Nat.testBit_two_pow_sub_one, ht]⟩,
        Or.inl hm⟩
    · exact ⟨0, ⟨hpos, fun t ht => by simp [PEqualNP.CircuitLowerBounds.GateOp.eval]⟩,
        Or.inl h0⟩
    · exact ⟨2 ^ T - 1, ⟨hmlt, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Nat.testBit_two_pow_sub_one, ht]⟩,
        Or.inl hm⟩
  · obtain ⟨a, ha, ha1, ha2⟩ := hinv i
    rcases hop with rfl | rfl | rfl
    · exact ⟨a, ⟨ha1, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, ha2 t ht]⟩, Or.inl ha⟩
    · exact ⟨a, ⟨ha1, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, ha2 t ht]⟩, Or.inl ha⟩
    · exact ⟨(2 ^ T - 1) ^^^ a, ⟨Nat.xor_lt_two_pow hmlt ha1, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Nat.testBit_xor,
          Nat.testBit_two_pow_sub_one, ht, ha2 t ht]⟩, Or.inr (Or.inr ⟨rfl, a, ha, rfl⟩)⟩
  · obtain ⟨a, ha, ha1, ha2⟩ := hinv i
    obtain ⟨b, hb, hb1, hb2⟩ := hinv j
    rcases hop with rfl | rfl | rfl
    · exact ⟨a &&& b, ⟨lt_of_le_of_lt Nat.and_le_left ha1, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Nat.testBit_and, ha2 t ht, hb2 t ht]⟩,
        Or.inr (Or.inl ⟨by simp, a, ha, b, hb, Or.inl rfl⟩)⟩
    · exact ⟨a ||| b, ⟨Nat.or_lt_two_pow ha1 hb1, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Nat.testBit_or, ha2 t ht, hb2 t ht]⟩,
        Or.inr (Or.inl ⟨by simp, a, ha, b, hb, Or.inr rfl⟩)⟩
    · exact ⟨(2 ^ T - 1) ^^^ a, ⟨Nat.xor_lt_two_pow hmlt ha1, fun t ht => by
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Nat.testBit_xor,
          Nat.testBit_two_pow_sub_one, ht, ha2 t ht]⟩, Or.inr (Or.inr ⟨rfl, a, ha, rfl⟩)⟩
  · simp at hlen

theorem PEqualNP.Outside.L_meta_50488.sound (T : ℕ) (outs : List ℕ) (hnd : outs.Nodup)
    (hlt : ∀ o ∈ outs, o < 2 ^ T) :
    ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W : ℕ → List Bool) (S : List ℕ)
      (G k L : ℕ),
      (∀ t < T, (W t).length = L) → 0 ∈ S → 2 ^ T - 1 ∈ S →
      (∀ i, ∃ c ∈ S, c < 2 ^ T ∧ ∀ t < T, c.testBit t = (W t).getD i false) →
      (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
      gs.length ≤ G →
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ k →
      (∀ o ∈ outs, ∃ i, ∀ t < T,
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (W t)).getD i false = o.testBit t) →
      PEqualNP.Outside.L_meta_50488.reach (2 ^ T - 1) outs G k S = true := by
  intro gs
  induction gs with
  | nil =>
    intro W S G k L _ _ _ hinv _ _ _ hout
    have hall : (outs.all fun o => S.contains o) = true := by
      rw [List.all_eq_true]
      intro o ho
      obtain ⟨i, hi⟩ := hout o ho
      obtain ⟨c, hc, hc1, hc2⟩ := hinv i
      have hco : c = o := by
        apply Nat.eq_of_testBit_eq
        intro t
        by_cases ht : t < T
        · rw [hc2 t ht]; exact hi t ht
        · have hT : 2 ^ T ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc1 hT),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (hlt o ho) hT)]
      subst hco
      simpa using hc
    cases G with
    | zero => simp only [PEqualNP.Outside.L_meta_50488.reach]; exact hall
    | succ G => simp only [PEqualNP.Outside.L_meta_50488.reach, hall, Bool.true_or]
  | cons g gs ih =>
    intro W S G k L hL h0 hm hinv hfan hlen hnot hout
    obtain ⟨c, ⟨hc1, hc2⟩, hcl⟩ :=
      PEqualNP.Outside.L_meta_50488.gate T W S h0 hm hinv g (hfan g (by simp))
    have hL' : ∀ t < T,
        (W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]).length = L + 1 := by
      intro t ht; simp [hL t ht]
    have hfan' : ∀ g' ∈ gs, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g'.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g'.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')
    have hinvS : ∀ S' : List ℕ, (∀ x ∈ S, x ∈ S') → c ∈ S' → ∀ i, ∃ c' ∈ S', c' < 2 ^ T ∧
        ∀ t < T, c'.testBit t =
          (W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]).getD i false := by
      intro S' hsub hcS i
      by_cases hi : i = L
      · refine ⟨c, hcS, hc1, fun t ht => ?_⟩
        rw [hc2 t ht, PEqualNP.Outside.L_meta_50488.getD_snoc]
        simp [hL t ht, hi]
      · obtain ⟨a, ha, ha1, ha2⟩ := hinv i
        refine ⟨a, hsub a ha, ha1, fun t ht => ?_⟩
        rw [ha2 t ht, PEqualNP.Outside.L_meta_50488.getD_snoc]
        simp [hL t ht, hi]
    have hlen1 : gs.length + 1 ≤ G := by simpa using hlen
    have hnc : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤
        PEqualNP.NotBracket.notCount ⟨g :: gs, 0⟩ := by
      simp only [PEqualNP.NotBracket.notCount, List.filter_cons]
      split <;> simp
    have hin : c ∈ S → PEqualNP.Outside.L_meta_50488.reach (2 ^ T - 1) outs G k S = true :=
      fun hcS => ih _ S G k (L + 1) hL' h0 hm (hinvS S (fun _ h => h) hcS) hfan' (by omega)
        (le_trans hnc hnot) hout
    by_cases hcS : c ∈ S
    · exact hin hcS
    · obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      have hstep : ∀ k', PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ k' →
          PEqualNP.Outside.L_meta_50488.reach (2 ^ T - 1) outs G' k' (c :: S) = true :=
        fun k' hk' => ih _ (c :: S) G' k' (L + 1) hL' (List.mem_cons_of_mem _ h0)
          (List.mem_cons_of_mem _ hm)
          (hinvS (c :: S) (fun _ h => List.mem_cons_of_mem _ h) (List.mem_cons_self ..)) hfan'
          (by omega) hk' hout
      have hmiss : ∀ k',
          PEqualNP.Outside.L_meta_50488.reach (2 ^ T - 1) outs G' k' (c :: S) = true →
          (outs.filter fun o => !S.contains o).length ≤ G' + 1 := by
        intro k' hr
        have h1 := PEqualNP.Outside.L_meta_50488.reach_miss _ _ _ _ _ hr
        have h2 := PEqualNP.Outside.L_meta_50488.miss_cons outs hnd c S
        omega
      simp only [PEqualNP.Outside.L_meta_50488.reach, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, List.any_eq_true]
      rcases hcl with hcS' | ⟨hop, a, ha, b, hb, hab⟩ | ⟨hop, a, ha, hca⟩
      · exact absurd hcS' hcS
      · have hr := hstep k (le_trans hnc hnot)
        refine Or.inr ⟨hmiss k hr, Or.inl ⟨c, ?_, hr⟩⟩
        simp only [PEqualNP.Outside.L_meta_50488.cands, List.mem_dedup, List.mem_filter,
          List.mem_flatMap]
        refine ⟨⟨a, ha, b, hb, by simpa using hab⟩, by simpa using hcS⟩
      · have hk : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + 1 ≤ k := by
          have : PEqualNP.NotBracket.notCount ⟨g :: gs, 0⟩ =
              PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + 1 := by
            simp [PEqualNP.NotBracket.notCount, hop]
          omega
        have hr := hstep (k - 1) (by omega)
        refine Or.inr ⟨hmiss (k - 1) hr, Or.inr ⟨by omega, c, ?_, hr⟩⟩
        simp only [PEqualNP.Outside.L_meta_50488.ncands, List.mem_filter, List.mem_map]
        exact ⟨⟨a, ha, hca.symm⟩, by simpa using hcS⟩

theorem PEqualNP.Outside.L_meta_50488.init : ∀ i, ∃ c ∈ ([62, 60, 56, 48, 32, 0, 63] : List ℕ), c < 2 ^ 6 ∧
    ∀ t < 6, c.testBit t =
      ((List.ofFn (fun i : Fin 5 => decide (i.val < t))) ++ [false, true]).getD i false := by
  intro i
  by_cases hi : i < 5 + 2
  · interval_cases i <;> decide
  · refine ⟨0, by decide, by decide, fun t _ => ?_⟩
    rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_50488.none :
    PEqualNP.Outside.L_meta_50488.reach (2 ^ 6 - 1) [2, 34, 54] 5 2 [62, 60, 56, 48, 32, 0, 63] = false := by
  decide +kernel

theorem PEqualNP.Outside.L_meta_50488 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (34 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, h⟩
  have key := PEqualNP.Outside.L_meta_50488.sound 6 [2, 34, 54] (by decide) (by decide) D.gates
    (fun t => (List.ofFn (fun i : Fin 5 => decide (i.val < t))) ++ [false, true])
    [62, 60, 56, 48, 32, 0, 63] 5 2 (5 + 2) (by intro t _; simp) (by decide) (by decide)
    PEqualNP.Outside.L_meta_50488.init
    (fun g hg => by
      have := hfan g hg
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this)
    hsize hnot
    (by
      intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · exact ⟨p.val, fun t ht => (h ⟨t, ht⟩).1⟩
      · exact ⟨q.val, fun t ht => (h ⟨t, ht⟩).2.1⟩
      · exact ⟨r.val, fun t ht => (h ⟨t, ht⟩).2.2⟩)
  rw [PEqualNP.Outside.L_meta_50488.none] at key
  exact Bool.false_ne_true key
