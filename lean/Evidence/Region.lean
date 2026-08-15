import BMS.Expand
/-
Evidence/Region.lean — THE REGION BELOW ε_ω, NAMED

`Evidence/Cert.lean` §20.3 measured the ε₁ row's expansion closure and closed with
"the twelve non-`famM` matrices are the region this file cannot yet name, and naming a
region is all that is left".  This file names it.

WHAT THE REGION IS.  In Buchholz-tree coordinates the closure is exactly

    ψ₀(ξ)   for   ξ < Ω·ω,        summed

— matrices of width two whose row-1 entries are `0` or `1`, read as a forest by the
row-0 entries: a column `(d,0)` is a `ψ₀` node at depth `d`, a column `(d,1)` is `Ω`.
§16.5's finding that "`enc` is compositional in BUCHHOLZ-TREE coordinates, not in `φ̄`
coordinates" is the reason the index is this and not a `φ̄` recursion: the three clauses
that section REFUTED are all `φ̄`-shaped, and in these coordinates `mat` is one line.

    A            the index: `nil` = 0, `om r` = r ⊕ Ω, `ps r a` = r ⊕ ψ₀(a)
    mat t d      its matrix, read from depth `d`
    fs  t n      the fundamental sequence of the whole sum
    fsP a n      the fundamental sequence of the single principal ψ₀(a)

THE ONE THEOREM (`expand_mat`).  For every top-level index,

    BMS.expand? (mat t 0) n = some (mat (fs t n) 0)

so the family is closed under `BMS.expand` with a CLOSED description of the value —
which is exactly what `certIn_region`'s `Hclosed` asks for and what no Veblen-region row
could supply.  ε₁'s row `(0,0)(1,1)(1,1)` is `mat (ps nil (om (om nil))) 0`, and the
ε_ω row's expansions `epsM n` are `mat (ps nil (om^(n+1) nil)) 0`, so ONE region carries
both rows.

MEASURED BEFORE IT WAS PROVED, in the discipline of Cert.lean §22: over 100 indices
(the 91 top-level indices of size ≤ 3, plus nine hand-built deep ones) at `n ≤ 5`, with
the expansion closure taken to depth two — 0 failures, and the ONLY failure anywhere is
`t = nil`, where `expand?` is `none` and the region's `Hzero` takes over.  The
`#guard`s at the end of §5 are that measurement.

NO NORMAL-FORM CONDITION.  The identity needs neither descending summands nor any
condition on the prefix `P` in `expand_blk`: the bad root of `P ++ (a block at depth d)`
is the block's own root whatever `P` is, because `parent` takes the MAXIMUM earlier
column and every column of the block after the root sits at depth `> d`.  That is the
same sentence as §17.2's `parent_zero_append`, one depth up.
-/

namespace Evidence.Region

open BMS

/-! ## §1 The index, and its matrix

`A` is a SNOC list of summands: `ps r a` is "the sum `r`, then one more summand ψ₀(a)".
Snoc rather than cons because a fundamental sequence acts on the LAST summand, and this
puts it at the head of the pattern match. -/

/-- 領域の添字。`nil` = 0、`om r` = r ⊕ Ω、`ps r a` = r ⊕ ψ₀(a)。 -/
inductive A where
  | nil : A
  | om  : A → A
  | ps  : A → A → A
deriving DecidableEq, Repr, Inhabited

/-- 深さ `d` から読んだ行列。`ψ₀` の節は `(d,0)`、`Ω` は `(d,1)`。 -/
def mat : A → Nat → Matrix
  | .nil, _ => []
  | .om r, d => mat r d ++ [[d, 1]]
  | .ps r a, d => mat r d ++ ([d, 0] :: mat a (d + 1))

/-- 和の連結。 -/
def app : A → A → A
  | r, .nil => r
  | r, .om s => .om (app r s)
  | r, .ps s a => .ps (app r s) a

/-- `ψ₀(b)` を `n+1` 個並べた和。 -/
def rep (b : A) : Nat → A
  | 0 => .ps .nil b
  | k + 1 => .ps (rep b k) b

/-- Ω の段の塔。`iterOm b 0 = ψ₀(b)`、`iterOm b (k+1) = ψ₀(b ⊕ iterOm b k)`。 -/
def iterOm (b : A) : Nat → A
  | 0 => .ps .nil b
  | k + 1 => .ps .nil (app b (iterOm b k))

/-- 主要項 `ψ₀(a)` の基本列 (`a ≠ nil` で意味を持つ)。和として返る。 -/
def fsP : A → Nat → A
  | .nil, _ => .nil
  | .om b, n => iterOm b n
  | .ps b .nil, n => rep b n
  | .ps b c, n => .ps .nil (app b (fsP c n))

/-- 和全体の基本列。最後の加数に作用する。 -/
def fs : A → Nat → A
  | .nil, _ => .nil
  | .om _, _ => .nil
  | .ps r .nil, _ => r
  | .ps r a, n => app r (fsP a n)

/-- 最上位の形: Ω は最上位の加数にはならない。 -/
def topOK : A → Bool
  | .nil => true
  | .om _ => false
  | .ps r _ => topOK r

/-- 行 0 を `e` だけ上げる。 -/
def shc (e : Nat) (c : Col) : Col := (c.getD 0 0 + e) :: c.drop 1

/-- 行列全体の行 0 を `e` だけ上げる。 -/
def sh (e : Nat) (M : Matrix) : Matrix := M.map (shc e)

/-! ## §2 The algebra of `mat` -/

theorem sh_append (e : Nat) (M N : Matrix) : sh e (M ++ N) = sh e M ++ sh e N :=
  List.map_append

theorem sh_cons (e : Nat) (c : Col) (M : Matrix) : sh e (c :: M) = shc e c :: sh e M := rfl

theorem shc_pair (e a b : Nat) : shc e [a, b] = [a + e, b] := rfl

/-- 深さは行 0 のずらしにすぎない。 -/
theorem mat_sh : ∀ (t : A) (d e : Nat), mat t (d + e) = sh e (mat t d) := by
  intro t
  induction t with
  | nil => intro d e; rfl
  | om r ih =>
    intro d e
    show mat r (d + e) ++ [[d + e, 1]] = sh e (mat r d ++ [[d, 1]])
    rw [sh_append, ih d e]
    rfl
  | ps r a ihr iha =>
    intro d e
    show mat r (d + e) ++ ([d + e, 0] :: mat a (d + e + 1))
      = sh e (mat r d ++ ([d, 0] :: mat a (d + 1)))
    rw [sh_append, ihr d e, sh_cons, shc_pair,
      show d + e + 1 = d + 1 + e from by omega, iha (d + 1) e]

theorem app_nil : ∀ (s : A), app .nil s = s := by
  intro s
  induction s with
  | nil => rfl
  | om s ih => show A.om (app .nil s) = _; rw [ih]
  | ps s a ih _ => show A.ps (app .nil s) a = _; rw [ih]

/-- 連結は行列の連結。 -/
theorem mat_app : ∀ (s r : A) (d : Nat), mat (app r s) d = mat r d ++ mat s d := by
  intro s
  induction s with
  | nil => intro r d; exact (List.append_nil _).symm
  | om s ih =>
    intro r d
    show mat (app r s) d ++ [[d, 1]] = mat r d ++ (mat s d ++ [[d, 1]])
    rw [ih r d, List.append_assoc]
  | ps s a ih _ =>
    intro r d
    show mat (app r s) d ++ ([d, 0] :: mat a (d + 1))
      = mat r d ++ (mat s d ++ ([d, 0] :: mat a (d + 1)))
    rw [ih r d, List.append_assoc]

/-- 列はすべて高さ 2。 -/
theorem mat_col_len : ∀ (t : A) (d : Nat), ∀ c ∈ mat t d, c.length = 2 := by
  intro t
  induction t with
  | nil => intro d c hc; exact absurd hc (by simp [mat])
  | om r ih =>
    intro d c hc
    rcases List.mem_append.mp hc with h | h
    · exact ih d c h
    · rcases List.mem_singleton.mp h with rfl; rfl
  | ps r a ihr iha =>
    intro d c hc
    rcases List.mem_append.mp hc with h | h
    · exact ihr d c h
    · rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact iha (d + 1) c h

/-- 行 0 の値は深さ以上。 -/
theorem mat_col_lb : ∀ (t : A) (d : Nat), ∀ c ∈ mat t d, d ≤ c.getD 0 0 := by
  intro t
  induction t with
  | nil => intro d c hc; exact absurd hc (by simp [mat])
  | om r ih =>
    intro d c hc
    rcases List.mem_append.mp hc with h | h
    · exact ih d c h
    · rcases List.mem_singleton.mp h with rfl; exact Nat.le_refl d
  | ps r a ihr iha =>
    intro d c hc
    rcases List.mem_append.mp hc with h | h
    · exact ihr d c h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_refl d
      · exact Nat.le_of_succ_le (iha (d + 1) c h)

/-- 前から 1 つはがす。 -/
theorem flatten_range_succ (g : Nat → Matrix) (n : Nat) :
    ((List.range (n + 1)).map g).flatten
      = g 0 ++ ((List.range n).map (fun k => g (k + 1))).flatten := by
  rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
  rfl

/-- `ψ₀(b)` を `n+1` 個並べた行列。 -/
theorem flatten_rep (b : A) (d : Nat) : ∀ (n : Nat),
    ((List.range (n + 1)).map (fun _ => mat (.ps .nil b) d)).flatten = mat (rep b n) d := by
  intro n
  induction n with
  | zero => show mat (.ps .nil b) d ++ [] = _; rw [List.append_nil]; rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    show mat (rep b k) d ++ (mat (.ps .nil b) d ++ []) = mat (rep b k) d ++ ([d, 0] :: mat b (d + 1))
    rw [List.append_nil]
    rfl

/-- Ω 塔の行列: `m` 番目の複製は深さが `m` だけ深い。 -/
theorem flatten_iterOm (b : A) : ∀ (d n : Nat),
    ((List.range (n + 1)).map (fun m => sh m (mat (.ps .nil b) d))).flatten
      = mat (iterOm b n) d := by
  intro d n
  induction n generalizing d with
  | zero =>
    show sh 0 (mat (.ps .nil b) d) ++ [] = mat (.ps .nil b) d
    rw [List.append_nil, ← mat_sh (.ps .nil b) d 0]
    rfl
  | succ k ih =>
    rw [flatten_range_succ]
    show sh 0 (mat (.ps .nil b) d)
        ++ ((List.range (k + 1)).map (fun m => sh (m + 1) (mat (.ps .nil b) d))).flatten
      = [d, 0] :: mat (app b (iterOm b k)) (d + 1)
    rw [← mat_sh (.ps .nil b) d 0, mat_app (iterOm b k) b (d + 1)]
    rw [show ((List.range (k + 1)).map (fun m => sh (m + 1) (mat (.ps .nil b) d))).flatten
        = ((List.range (k + 1)).map (fun m => sh m (mat (.ps .nil b) (d + 1)))).flatten from by
      refine congrArg List.flatten (List.map_congr_left ?_)
      intro m _
      rw [← mat_sh (.ps .nil b) d (m + 1), ← mat_sh (.ps .nil b) (d + 1) m,
        show d + (m + 1) = d + 1 + m from by omega]]
    rw [ih (d + 1)]
    rfl

/-! ## §3 A local toolkit

`Evidence/Cert.lean` §17.2–§17.3 has all of this, but that file will IMPORT this one, so
the copies are here.  They are short and mechanical. -/

theorem getD_append_right {α : Type} (P Q : List α) (j : Nat) (v : α)
    (h : P.length ≤ j) : (P ++ Q).getD j v = Q.getD (j - P.length) v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem ent_append (P Q : Matrix) (j y : Nat) (h : P.length ≤ j) :
    ent (P ++ Q) j y = ent Q (j - P.length) y := by
  show ((P ++ Q).getD j []).getD y 0 = _
  rw [getD_append_right P Q j [] h]
  rfl

theorem take_left_len (P Q : Matrix) : (P ++ Q).take P.length = P := by
  simp

theorem iterParent_nil {f : Nat → Option Nat} {fuel x : Nat} (h : f x = none) :
    iterParent f fuel x = [] := by
  cases fuel with
  | zero => rfl
  | succ g => show (match f x with | none => [] | some p => p :: iterParent f g p) = []
              rw [h]

theorem iterParent_cons {f : Nat → Option Nat} {fuel x q : Nat} (h : f x = some q) :
    iterParent f (fuel + 1) x = q :: iterParent f fuel q := by
  show (match f x with | none => [] | some p => p :: iterParent f fuel p) = _
  rw [h]

theorem iterParent_lt {f : Nat → Option Nat} (hdec : ∀ z w, f z = some w → w < z) :
    ∀ (fuel x p : Nat), p ∈ iterParent f fuel x → p < x := by
  intro fuel
  induction fuel with
  | zero => intro x p hp; exact absurd hp (by simp [iterParent])
  | succ g ih =>
    intro x p hp
    cases hfx : f x with
    | none => rw [iterParent_nil hfx] at hp; exact absurd hp (by simp)
    | some q =>
      rw [iterParent_cons hfx] at hp
      rcases List.mem_cons.mp hp with h | h
      · rw [h]; exact hdec x q hfx
      · exact Nat.lt_trans (ih q p h) (hdec x q hfx)

theorem parent_lt : ∀ (M : Matrix) (y x r : Nat), parent M y x = some r → r < x := by
  intro M y
  induction y with
  | zero =>
    intro x r h
    have h' : (((List.range x).filter
        (fun p => decide (ent M p 0 < ent M x 0))).max?) = some r := h
    obtain ⟨hmem, _⟩ := List.max?_eq_some_iff.mp h'
    rw [List.mem_filter, List.mem_range] at hmem
    exact hmem.1
  | succ y ih =>
    intro x r h
    have h' : (((iterParent (parent M y) x x).filter
        (fun p => decide (ent M p (y + 1) < ent M x (y + 1)))).max?) = some r := h
    obtain ⟨hmem, _⟩ := List.max?_eq_some_iff.mp h'
    rw [List.mem_filter] at hmem
    exact iterParent_lt (fun z w hw => ih z w hw) x x r hmem.1

theorem map_getD_range_map {α β : Type} (v : α) (g : α → β) : ∀ (l : List α),
    (List.range l.length).map (fun x => g (l.getD x v)) = l.map g := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    show (List.range (t.length + 1)).map (fun x => g ((a :: t).getD x v)) = g a :: t.map g
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    exact congrArg (g a :: ·) ih

theorem map_getD_range {α : Type} (v : α) :
    ∀ (l : List α), (List.range l.length).map (fun x => l.getD x v) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    show (List.range (t.length + 1)).map (fun x => (a :: t).getD x v) = a :: t
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    exact congrArg (a :: ·) ih

/-- 高さ 2 の列は 2 つの成分で決まる。 -/
theorem col2 (c : Col) (h : c.length = 2) : [c.getD 0 0, c.getD 1 0] = c := by
  match c, h with
  | [_, _], _ => rfl

theorem shc_len2 (e : Nat) (c : Col) (h : c.length = 2) :
    shc e c = [c.getD 0 0 + e, c.getD 1 0] := by
  match c, h with
  | [_, _], _ => rfl

/-- 高さ 2 の列だけからなる行列の、`lnz` の値。 -/
theorem lnz_pair (a b : Nat) :
    lnz [a, b] = if 0 < b then some 1 else if 0 < a then some 0 else none := by
  cases a with
  | zero => cases b with | zero => rfl | succ _ => rfl
  | succ _ => cases b with | zero => rfl | succ _ => rfl

/-! ## §4 The bad root of `P ++ Bk ++ [last]`

`Bk` is a principal block at depth `d`: its first column is `(d,0)` and every later one
sits at depth `≥ d+1`.  `last` is the column that ends the matrix, again at depth `d+1`.
Then the bad root is `Bk`'s own root — WHATEVER `P` IS.  `parent` takes the MAXIMUM
earlier column with a smaller entry, `Bk`'s root is such a column, and no column between
it and the end is: that is the whole argument, and it never looks at `P`. -/

section Frame

set_option linter.unusedSectionVars false

variable (P Bk : Matrix) (d : Nat) (last : Col)

/-- 骨組みの行列。 -/
local notation "SS" => P ++ (Bk ++ [last])

theorem frame_len : (P ++ (Bk ++ [last])).length = P.length + Bk.length + 1 := by
  rw [List.length_append, List.length_append, List.length_cons, List.length_nil]
  omega

theorem frame_ent (x y : Nat) (hx : x < Bk.length) :
    ent (P ++ (Bk ++ [last])) (P.length + x) y = ent Bk x y := by
  rw [ent_append P _ _ _ (by omega), show P.length + x - P.length = x from by omega]
  show ((Bk ++ [last]).getD x []).getD y 0 = _
  rw [show (Bk ++ [last]).getD x [] = Bk.getD x [] from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hx]]
  rfl

theorem frame_ent_last (y : Nat) :
    ent (P ++ (Bk ++ [last])) (P.length + Bk.length) y = last.getD y 0 := by
  rw [ent_append P _ _ _ (by omega), show P.length + Bk.length - P.length = Bk.length from by omega]
  show ((Bk ++ [last]).getD Bk.length []).getD y 0 = _
  rw [getD_append_right Bk [last] Bk.length [] (Nat.le_refl _),
    show Bk.length - Bk.length = 0 from by omega]
  rfl

theorem frame_getLast : (P ++ (Bk ++ [last])).getLast? = some last := by
  rw [show P ++ (Bk ++ [last]) = (P ++ Bk) ++ [last] from by rw [List.append_assoc]]
  simp

variable (hroot : Bk.getD 0 [] = [d, 0])
  (hin : ∀ i, 0 < i → i < Bk.length → d + 1 ≤ ent Bk i 0)
  (hlast : last.getD 0 0 = d + 1)
  (hBk : 0 < Bk.length)

include hroot hin hlast hBk

/-- **行 0 の悪根は `Bk` の根。** `P` には条件がいらない。 -/
theorem frame_parent0 :
    parent (P ++ (Bk ++ [last])) 0 (P.length + Bk.length) = some P.length := by
  have hE : ent (P ++ (Bk ++ [last])) (P.length + Bk.length) 0 = d + 1 := by
    rw [frame_ent_last P Bk last 0]; exact hlast
  have hr0 : ent (P ++ (Bk ++ [last])) P.length 0 = d := by
    rw [show P.length = P.length + 0 from by omega, frame_ent P Bk last 0 0 hBk]
    show (Bk.getD 0 []).getD 0 0 = d
    rw [hroot]; rfl
  show ((List.range (P.length + Bk.length)).filter
      (fun p => decide (ent (P ++ (Bk ++ [last])) p 0
        < ent (P ++ (Bk ++ [last])) (P.length + Bk.length) 0))).max? = some P.length
  rw [hE]
  refine List.max?_eq_some_iff.mpr ⟨?_, ?_⟩
  · rw [List.mem_filter, List.mem_range]
    refine ⟨by omega, ?_⟩
    rw [hr0]
    simp only [decide_eq_true_eq]
    omega
  · intro b hb
    rw [List.mem_filter, List.mem_range] at hb
    rcases Nat.lt_or_ge P.length b with h | h
    · exfalso
      have hb2 : b - P.length < Bk.length := by omega
      have hge := hin (b - P.length) (by omega) hb2
      have heq := frame_ent P Bk last (b - P.length) 0 hb2
      rw [show P.length + (b - P.length) = b from by omega] at heq
      have h2 := hb.2
      simp only [decide_eq_true_eq, heq] at h2
      omega
    · exact h

/-- 行 0 の親鎖は `Bk` の根に届く。 -/
theorem frame_chain : ∀ (fuel x : Nat), x ≤ fuel → P.length < x → x < P.length + Bk.length →
    (iterParent (parent (P ++ (Bk ++ [last])) 0) fuel x).contains P.length = true := by
  have hr0 : ent (P ++ (Bk ++ [last])) P.length 0 = d := by
    rw [show P.length = P.length + 0 from by omega, frame_ent P Bk last 0 0 hBk]
    show (Bk.getD 0 []).getD 0 0 = d
    rw [hroot]; rfl
  have hstep : ∀ x, P.length < x → x < P.length + Bk.length →
      ∃ q, parent (P ++ (Bk ++ [last])) 0 x = some q ∧ P.length ≤ q ∧ q < x := by
    intro x h1 h2
    have hx : ent (P ++ (Bk ++ [last])) x 0 ≥ d + 1 := by
      have hlt : x - P.length < Bk.length := by omega
      have := hin (x - P.length) (by omega) hlt
      rw [show x = P.length + (x - P.length) from by omega,
        frame_ent P Bk last (x - P.length) 0 hlt]
      exact this
    have hmem : P.length ∈ (List.range x).filter
        (fun p => decide (ent (P ++ (Bk ++ [last])) p 0 < ent (P ++ (Bk ++ [last])) x 0)) := by
      rw [List.mem_filter, List.mem_range]
      refine ⟨h1, ?_⟩
      rw [hr0]
      simp only [decide_eq_true_eq]
      omega
    cases hq : ((List.range x).filter
        (fun p => decide (ent (P ++ (Bk ++ [last])) p 0
          < ent (P ++ (Bk ++ [last])) x 0))).max? with
    | none => rw [List.max?_eq_none_iff.mp hq] at hmem; exact absurd hmem (by simp)
    | some q =>
      obtain ⟨hqm, hqmax⟩ := List.max?_eq_some_iff.mp hq
      rw [List.mem_filter, List.mem_range] at hqm
      exact ⟨q, hq, hqmax P.length hmem, hqm.1⟩
  intro fuel
  induction fuel with
  | zero => intro x h1 h2 h3; omega
  | succ g ih =>
    intro x h1 h2 h3
    obtain ⟨q, hq, hq1, hq2⟩ := hstep x h2 h3
    rw [iterParent_cons hq, List.contains_cons]
    rcases Nat.eq_or_lt_of_le hq1 with h | h
    · rw [← h]; simp
    · rw [ih q (by omega) h (by omega)]; exact Bool.or_true _

end Frame

/-! ## §5 The expansion identity

Two base cases and one recursion.  `expand_prin_succ` is the argument's last summand being
`ψ₀(0)` — the block repeats, with NO increment, because `t = 0` makes `delta` vanish
identically.  `expand_prin_om` is the last summand being `Ω` — the block repeats WITH a
uniform `+m` on row 0, which is Buchholz's Ω-tower.  Everything else recurses one depth
down, and that is where the prefix grows. -/

theorem expand?_succ (M : Matrix) (L : Col)
    (hL : M.getLast? = some L) (ht : lnz L = none) (n : Nat) :
    expand? M n = some M.dropLast := by
  unfold BMS.expand?
  rw [hL]
  show (match lnz L with
    | none => some M.dropLast
    | some t => (parent M t (M.length - 1)).bind (fun r =>
        some (M.take r ++ ((List.range (n + 1)).map (fun a =>
          (List.range (M.length - 1 - r)).map fun x =>
            (List.range L.length).map fun y =>
              ent M (r + x) y + a * delta M r t y *
                (if ascends M r (r + x) y then 1 else 0))).flatten))) = some M.dropLast
  rw [ht]

theorem expand?_lim (M : Matrix) (L : Col) (t r : Nat)
    (hL : M.getLast? = some L) (ht : lnz L = some t)
    (hr : parent M t (M.length - 1) = some r) (n : Nat) :
    expand? M n = some (M.take r ++ ((List.range (n + 1)).map (fun a =>
      (List.range (M.length - 1 - r)).map fun x =>
        (List.range L.length).map fun y =>
          ent M (r + x) y + a * delta M r t y *
            (if ascends M r (r + x) y then 1 else 0))).flatten) := by
  unfold BMS.expand?
  rw [hL]
  show (match lnz L with
    | none => some M.dropLast
    | some t => (parent M t (M.length - 1)).bind (fun r =>
        some (M.take r ++ ((List.range (n + 1)).map (fun a =>
          (List.range (M.length - 1 - r)).map fun x =>
            (List.range L.length).map fun y =>
              ent M (r + x) y + a * delta M r t y *
                (if ascends M r (r + x) y then 1 else 0))).flatten))) = _
  rw [ht]
  show (parent M t (M.length - 1)).bind (fun r =>
      some (M.take r ++ ((List.range (n + 1)).map (fun a =>
        (List.range (M.length - 1 - r)).map fun x =>
          (List.range L.length).map fun y =>
            ent M (r + x) y + a * delta M r t y *
              (if ascends M r (r + x) y then 1 else 0))).flatten)) = _
  rw [hr]
  rfl

theorem getD_mem {α : Type} : ∀ (l : List α) (v : α) (j : Nat), j < l.length → l.getD j v ∈ l := by
  intro l
  induction l with
  | nil => intro v j h; exact absurd h (by simp)
  | cons a t ih =>
    intro v j h
    cases j with
    | zero => show a ∈ a :: t; exact List.Mem.head _
    | succ i =>
      show t.getD i v ∈ a :: t
      refine List.Mem.tail a (ih v i ?_)
      have hl : (a :: t).length = t.length + 1 := by simp
      omega

/-- ブロック `mat (ps nil b) d` の 3 つの性質。 -/
theorem blk_root (b : A) (d : Nat) : (mat (.ps .nil b) d).getD 0 [] = [d, 0] := rfl

theorem blk_pos (b : A) (d : Nat) : 0 < (mat (.ps .nil b) d).length := by
  show 0 < ([d, 0] :: mat b (d + 1)).length
  simp

theorem blk_len2 (b : A) (d : Nat) : ∀ c ∈ mat (.ps .nil b) d, c.length = 2 :=
  mat_col_len (.ps .nil b) d

theorem blk_len (b : A) (d : Nat) :
    (mat (.ps .nil b) d).length = (mat b (d + 1)).length + 1 := by
  show ([d, 0] :: mat b (d + 1)).length = _
  simp

theorem blk_in (b : A) (d : Nat) : ∀ i, 0 < i → i < (mat (.ps .nil b) d).length →
    d + 1 ≤ ent (mat (.ps .nil b) d) i 0 := by
  intro i h1 h2
  have hl := blk_len b d
  match i, h1 with
  | j + 1, _ =>
    have hj : j < (mat b (d + 1)).length := by omega
    show (((mat b (d + 1)).getD j []).getD 0 0) ≥ d + 1
    exact mat_col_lb b (d + 1) _ (getD_mem _ [] j hj)

/-- **後続の底、抽象版。** `t = 0` なので `delta` が恒等的に 0 になり、増分が生じない。
    ブロックがそのまま `n+1` 回並ぶ。前置き `P` には条件がない。 -/
theorem expand_frame_zero (P Bk : Matrix) (d : Nat)
    (hroot : Bk.getD 0 [] = [d, 0])
    (hin : ∀ i, 0 < i → i < Bk.length → d + 1 ≤ ent Bk i 0)
    (hlen2 : ∀ c ∈ Bk, c.length = 2)
    (hk : 0 < Bk.length) (n : Nat) :
    expand? (P ++ (Bk ++ [[d + 1, 0]])) n
      = some (P ++ ((List.range (n + 1)).map (fun _ => Bk)).flatten) := by
  have hlen := frame_len P Bk [d + 1, 0]
  have hlast : (([d + 1, 0] : Col)).getD 0 0 = d + 1 := rfl
  have hpar : parent (P ++ (Bk ++ [[d + 1, 0]])) 0 (P.length + Bk.length) = some P.length :=
    frame_parent0 P Bk d [d + 1, 0] hroot hin hlast hk
  rw [expand?_lim _ [d + 1, 0] 0 P.length
      (frame_getLast P Bk [d + 1, 0]) (by rw [lnz_pair]; simp)
      (by rw [hlen]; simpa using hpar) n]
  rw [take_left_len]
  refine congrArg some (congrArg (P ++ ·) ?_)
  have hblock : ∀ (a : Nat),
      (List.range ((P ++ (Bk ++ [[d + 1, 0]])).length - 1 - P.length)).map (fun x =>
        (List.range ([d + 1, 0] : Col).length).map fun y =>
          ent (P ++ (Bk ++ [[d + 1, 0]])) (P.length + x) y
            + a * delta (P ++ (Bk ++ [[d + 1, 0]])) P.length 0 y
              * (if ascends (P ++ (Bk ++ [[d + 1, 0]])) P.length (P.length + x) y then 1 else 0))
      = Bk := by
    intro a
    rw [show (P ++ (Bk ++ [[d + 1, 0]])).length - 1 - P.length = Bk.length from by
      rw [hlen]; omega]
    refine Eq.trans (List.map_congr_left ?_) (map_getD_range [] Bk)
    intro x hx
    rw [List.mem_range] at hx
    rw [show (List.range ([d + 1, 0] : Col).length) = [0, 1] from rfl]
    have hd : ∀ y, delta (P ++ (Bk ++ [[d + 1, 0]])) P.length 0 y = 0 := by
      intro y; simp [BMS.delta]
    have he : ∀ y, ent (P ++ (Bk ++ [[d + 1, 0]])) (P.length + x) y = (Bk.getD x []).getD y 0 := by
      intro y; rw [frame_ent P Bk [d + 1, 0] x y hx]; rfl
    simp only [List.map_cons, List.map_nil, hd, he,
      Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    exact col2 (Bk.getD x []) (hlen2 _ (getD_mem Bk [] x hx))
  rw [List.map_congr_left (fun a _ => hblock a)]

/-- **Ω の底、抽象版。** `t = 1` なので `delta` は行 0 で 1、行 1 で 0。根はブロック
    全体の行 0 の祖先なので、`m` 番目の複製は行 0 が一様に `m` 上がる。 -/
theorem expand_frame_one (P Bk : Matrix) (d : Nat)
    (hroot : Bk.getD 0 [] = [d, 0])
    (hin : ∀ i, 0 < i → i < Bk.length → d + 1 ≤ ent Bk i 0)
    (hlen2 : ∀ c ∈ Bk, c.length = 2)
    (hk : 0 < Bk.length) (n : Nat) :
    expand? (P ++ (Bk ++ [[d + 1, 1]])) n
      = some (P ++ ((List.range (n + 1)).map (fun m => sh m Bk)).flatten) := by
  have hlen := frame_len P Bk [d + 1, 1]
  have hlast : (([d + 1, 1] : Col)).getD 0 0 = d + 1 := rfl
  have hp0 : parent (P ++ (Bk ++ [[d + 1, 1]])) 0 (P.length + Bk.length) = some P.length :=
    frame_parent0 P Bk d [d + 1, 1] hroot hin hlast hk
  have hentP1 : ent (P ++ (Bk ++ [[d + 1, 1]])) P.length 1 = 0 := by
    rw [show P.length = P.length + 0 from by omega, frame_ent P Bk [d + 1, 1] 0 1 hk]
    show (Bk.getD 0 []).getD 1 0 = 0
    rw [hroot]; rfl
  have hentL1 : ent (P ++ (Bk ++ [[d + 1, 1]])) (P.length + Bk.length) 1 = 1 :=
    frame_ent_last P Bk [d + 1, 1] 1
  have hentL0 : ent (P ++ (Bk ++ [[d + 1, 1]])) (P.length + Bk.length) 0 = d + 1 :=
    frame_ent_last P Bk [d + 1, 1] 0
  have hentP0 : ent (P ++ (Bk ++ [[d + 1, 1]])) P.length 0 = d := by
    rw [show P.length = P.length + 0 from by omega, frame_ent P Bk [d + 1, 1] 0 0 hk]
    show (Bk.getD 0 []).getD 0 0 = d
    rw [hroot]; rfl
  have hp1 : parent (P ++ (Bk ++ [[d + 1, 1]])) 1 (P.length + Bk.length) = some P.length := by
    show ((iterParent (parent (P ++ (Bk ++ [[d + 1, 1]])) 0)
        (P.length + Bk.length) (P.length + Bk.length)).filter
        (fun q => decide (ent (P ++ (Bk ++ [[d + 1, 1]])) q 1
          < ent (P ++ (Bk ++ [[d + 1, 1]])) (P.length + Bk.length) 1))).max? = some P.length
    rw [hentL1]
    obtain ⟨u, hu⟩ : ∃ u, P.length + Bk.length = u + 1 := ⟨P.length + Bk.length - 1, by omega⟩
    rw [hu, iterParent_cons (by rw [← hu]; exact hp0), List.filter_cons_of_pos (by
      rw [hentP1]; simp)]
    refine List.max?_eq_some_iff.mpr ⟨by simp, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with h | h
    · omega
    · exact Nat.le_of_lt (iterParent_lt
        (fun w v hv => parent_lt _ 0 w v hv) u P.length z (List.mem_filter.mp h).1)
  rw [expand?_lim _ [d + 1, 1] 1 P.length
      (frame_getLast P Bk [d + 1, 1]) (by rw [lnz_pair]; simp)
      (by rw [hlen]; simpa using hp1) n]
  rw [take_left_len]
  refine congrArg some (congrArg (P ++ ·) ?_)
  have hblock : ∀ (a : Nat),
      (List.range ((P ++ (Bk ++ [[d + 1, 1]])).length - 1 - P.length)).map (fun x =>
        (List.range ([d + 1, 1] : Col).length).map fun y =>
          ent (P ++ (Bk ++ [[d + 1, 1]])) (P.length + x) y
            + a * delta (P ++ (Bk ++ [[d + 1, 1]])) P.length 1 y
              * (if ascends (P ++ (Bk ++ [[d + 1, 1]])) P.length (P.length + x) y then 1 else 0))
      = sh a Bk := by
    intro a
    rw [show (P ++ (Bk ++ [[d + 1, 1]])).length - 1 - P.length = Bk.length from by
      rw [hlen]; omega]
    show _ = Bk.map (shc a)
    refine Eq.trans (List.map_congr_left ?_) (map_getD_range_map [] (shc a) Bk)
    intro x hx
    rw [List.mem_range] at hx
    rw [show (List.range ([d + 1, 1] : Col).length) = [0, 1] from rfl]
    have hd0 : delta (P ++ (Bk ++ [[d + 1, 1]])) P.length 1 0 = 1 := by
      show (if 0 < 1 then ent (P ++ (Bk ++ [[d + 1, 1]]))
        ((P ++ (Bk ++ [[d + 1, 1]])).length - 1) 0 - _ else 0) = 1
      rw [if_pos (by omega), show (P ++ (Bk ++ [[d + 1, 1]])).length - 1
        = P.length + Bk.length from by rw [hlen]; omega, hentL0, hentP0]
      omega
    have hd1 : delta (P ++ (Bk ++ [[d + 1, 1]])) P.length 1 1 = 0 := by
      show (if 1 < 1 then _ else 0) = 0
      rw [if_neg (by omega)]
    have hasc : ascends (P ++ (Bk ++ [[d + 1, 1]])) P.length (P.length + x) 0 = true := by
      match x, hx with
      | 0, _ => show ((P.length + 0 == P.length) || _) = true
                simp
      | j + 1, hx =>
        show ((P.length + (j + 1) == P.length) || _) = true
        rw [frame_chain P Bk d [d + 1, 1] hroot hin hlast hk
          (P.length + (j + 1)) (P.length + (j + 1)) (Nat.le_refl _) (by omega) (by omega)]
        exact Bool.or_true _
    have he : ∀ y, ent (P ++ (Bk ++ [[d + 1, 1]])) (P.length + x) y = (Bk.getD x []).getD y 0 := by
      intro y; rw [frame_ent P Bk [d + 1, 1] x y hx]; rfl
    simp only [List.map_cons, List.map_nil, hd0, hd1, hasc, he,
      Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_one, if_true]
    rw [shc_len2 a (Bk.getD x []) (hlen2 _ (getD_mem Bk [] x hx))]
  rw [List.map_congr_left (fun a _ => hblock a)]

/-- **後続の底。** 引数の最後の加数が `ψ₀(0)` のとき、ブロックが `n+1` 回並ぶ。 -/
theorem expand_prin_succ (b : A) (P : Matrix) (d n : Nat) :
    expand? (P ++ mat (.ps .nil (.ps b .nil)) d) n = some (P ++ mat (rep b n) d) := by
  rw [show P ++ mat (.ps .nil (.ps b .nil)) d
      = P ++ (mat (.ps .nil b) d ++ [[d + 1, 0]]) from rfl,
    expand_frame_zero P (mat (.ps .nil b) d) d (blk_root b d) (blk_in b d)
      (blk_len2 b d) (blk_pos b d) n, flatten_rep b d n]

/-- **Ω の底。** 引数の最後の加数が `Ω` のとき、Buchholz の Ω 塔が出る。 -/
theorem expand_prin_om (b : A) (P : Matrix) (d n : Nat) :
    expand? (P ++ mat (.ps .nil (.om b)) d) n = some (P ++ mat (iterOm b n) d) := by
  rw [show P ++ mat (.ps .nil (.om b)) d
      = P ++ (mat (.ps .nil b) d ++ [[d + 1, 1]]) from rfl,
    expand_frame_one P (mat (.ps .nil b) d) d (blk_root b d) (blk_in b d)
      (blk_len2 b d) (blk_pos b d) n, flatten_iterOm b d n]

/-- **再帰。** 引数の最後の加数が `ψ₀(c)` (`c ≠ 0`) のとき、1 段深いところへ落ちる。
    前置きが伸びるのはここだけで、その前置きに条件はいらない。 -/
theorem expand_prin_deep (b c : A)
    (ih : ∀ (P : Matrix) (d n : Nat),
      expand? (P ++ mat (.ps .nil c) d) n = some (P ++ mat (fsP c n) d))
    (P : Matrix) (d n : Nat) :
    expand? (P ++ mat (.ps .nil (.ps b c)) d) n
      = some (P ++ mat (.ps .nil (app b (fsP c n))) d) := by
  have hS : P ++ mat (.ps .nil (.ps b c)) d
      = (P ++ mat (.ps .nil b) d) ++ mat (.ps .nil c) (d + 1) := by
    show P ++ ([d, 0] :: (mat b (d + 1) ++ ([d + 1, 0] :: mat c (d + 2))))
      = (P ++ ([d, 0] :: mat b (d + 1))) ++ ([d + 1, 0] :: mat c (d + 2))
    rw [List.append_assoc]
    rfl
  rw [hS, ih (P ++ mat (.ps .nil b) d) (d + 1) n]
  refine congrArg some ?_
  show (P ++ ([d, 0] :: mat b (d + 1))) ++ mat (fsP c n) (d + 1)
    = P ++ ([d, 0] :: mat (app b (fsP c n)) (d + 1))
  rw [List.append_assoc, mat_app (fsP c n) b (d + 1)]
  rfl

/-- **主要項の展開。** `ψ₀(a)` の行列は `fsP a n` の行列へ展開する。前置き `P` は任意。 -/
theorem expand_blk : ∀ (a : A), a ≠ .nil → ∀ (P : Matrix) (d n : Nat),
    expand? (P ++ mat (.ps .nil a) d) n = some (P ++ mat (fsP a n) d) := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | om b _ => intro _ P d n; exact expand_prin_om b P d n
  | ps b c _ ihc =>
    intro _ P d n
    cases c with
    | nil => exact expand_prin_succ b P d n
    | om c' =>
      show expand? (P ++ mat (.ps .nil (.ps b (.om c'))) d) n
        = some (P ++ mat (.ps .nil (app b (fsP (.om c') n))) d)
      exact expand_prin_deep b (.om c') (ihc (by intro h; exact A.noConfusion h)) P d n
    | ps c1 c2 =>
      show expand? (P ++ mat (.ps .nil (.ps b (.ps c1 c2))) d) n
        = some (P ++ mat (.ps .nil (app b (fsP (.ps c1 c2) n))) d)
      exact expand_prin_deep b (.ps c1 c2) (ihc (by intro h; exact A.noConfusion h)) P d n

/-- **領域は展開で閉じている。** これが `certIn_region` の `Hclosed` が求めるもの。 -/
theorem expand_mat : ∀ (t : A), topOK t = true → t ≠ .nil → ∀ (n : Nat),
    expand? (mat t 0) n = some (mat (fs t n) 0) := by
  intro t
  cases t with
  | nil => intro _ h; exact absurd rfl h
  | om r => intro h; exact Bool.noConfusion h
  | ps r a =>
    intro _ _ n
    cases a with
    | nil =>
      show expand? (mat r 0 ++ [[0, 0]]) n = some (mat r 0)
      rw [expand?_succ _ [0, 0] (by simp) (by rw [lnz_pair]; simp) n]
      simp
    | om a' =>
      show expand? (mat r 0 ++ mat (.ps .nil (.om a')) 0) n
        = some (mat (app r (fsP (.om a') n)) 0)
      rw [expand_blk (.om a') (by intro h; exact A.noConfusion h) (mat r 0) 0 n,
        mat_app (fsP (.om a') n) r 0]
    | ps a1 a2 =>
      show expand? (mat r 0 ++ mat (.ps .nil (.ps a1 a2)) 0) n
        = some (mat (app r (fsP (.ps a1 a2) n)) 0)
      rw [expand_blk (.ps a1 a2) (by intro h; exact A.noConfusion h) (mat r 0) 0 n,
        mat_app (fsP (.ps a1 a2) n) r 0]

/-! ## §6 THE MEASUREMENT, AND THE TWO ROWS

The `#guard`s are the measurement that preceded the proof, kept as a regression: every
top-level index of size ≤ 3 (91 of them) satisfies the identity at `n ≤ 5`, `fs` never
leaves the top-level shape, and the matrix `kind` agrees with the index's own reading of
itself.  The last is what `Hzero`/`Hsucc`/`Hlim` will dispatch on.

`omPow k` is `Ω·k`, so `ps nil (omPow (k+1))` is `ψ₀(Ω·(k+1))` = `ε_k`.  `eps1_row` and
`epsM_row` are the two rows this region was built for: the ε₁ row is the index at `k = 1`,
and `Evidence/Cert.lean` §20's `epsM n` — the ε_ω row's `n`-th expansion — is the index at
`k = n`. -/

/-- `Ω·k`。 -/
def omPow : Nat → A
  | 0 => .nil
  | k + 1 => .om (omPow k)

theorem mat_omPow (d : Nat) : ∀ (k : Nat), mat (omPow k) d = List.replicate k [d, 1] := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
    show mat (omPow j) d ++ [[d, 1]] = _
    rw [ih, List.replicate_succ']

/-- **ε₁ の行。** -/
theorem eps1_row : mat (.ps .nil (omPow 2)) 0 = [[0, 0], [1, 1], [1, 1]] := rfl

/-- **ε_k の行** — `Evidence/Cert.lean` §20 の `epsM k`。 -/
theorem epsM_row (k : Nat) :
    mat (.ps .nil (omPow (k + 1))) 0 = [[0, 0], [1, 1]] ++ (List.replicate k [[1, 1]]).flatten := by
  show [0, 0] :: mat (omPow (k + 1)) 1 = _
  rw [mat_omPow 1 (k + 1)]
  show ([0, 0] : Col) :: List.replicate (k + 1) [1, 1] = _
  rw [List.replicate_succ]
  refine congrArg (fun l => ([0, 0] : Col) :: ([1, 1] : Col) :: l) ?_
  induction k with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ih]; rfl

theorem topOK_ps_nil (a : A) : topOK (.ps .nil a) = true := rfl

theorem ps_ne_nil (r a : A) : (A.ps r a) ≠ .nil := by
  intro h; exact A.noConfusion h

/-- **ε₁ の行の展開** — 添字の側では Ω 塔になる。 -/
theorem expand_eps1 (n : Nat) :
    expand? [[0, 0], [1, 1], [1, 1]] n = some (mat (iterOm (omPow 1) n) 0) := by
  rw [← eps1_row, expand_mat (.ps .nil (omPow 2)) (topOK_ps_nil _) (ps_ne_nil _ _) n]
  show some (mat (app .nil (iterOm (omPow 1) n)) 0) = _
  rw [app_nil]

/-- **ε_k の行の展開。** -/
theorem expand_epsM (k n : Nat) :
    expand? ([[0, 0], [1, 1]] ++ (List.replicate k [[1, 1]]).flatten) n
      = some (mat (iterOm (omPow k) n) 0) := by
  rw [← epsM_row k, expand_mat (.ps .nil (omPow (k + 1))) (topOK_ps_nil _) (ps_ne_nil _ _) n]
  show some (mat (app .nil (iterOm (omPow k) n)) 0) = _
  rw [app_nil]

/-! ### The measurement -/

/-- 大きさ `n` までの添字を全部作る。 -/
def gen : Nat → List A
  | 0 => [.nil]
  | k + 1 =>
    let sm := gen k
    (sm ++ sm.map A.om ++ sm.flatMap (fun r => sm.map (fun a => A.ps r a))).eraseDups

/-- 最上位の形をした、`0` でない添字。 -/
def corpus : List A := ((gen 3).filter topOK).filter (fun t => t != .nil)

/-- 添字が自分で読む種別。 -/
def kindA : A → BMS.Kind
  | .nil => .zero
  | .ps _ .nil => .succ
  | _ => .lim

-- 91 個の最上位添字、`n ≤ 5` で展開の等式。
#guard corpus.length == 91
#guard corpus.all fun t => (List.range 6).all fun n =>
  BMS.expand? (mat t 0) n == some (mat (fs t n) 0)
-- `fs` は最上位の形を保つ (`Hclosed`)。
#guard corpus.all fun t => (List.range 6).all fun n => topOK (fs t n)
-- 行列の種別は添字の種別と一致する。
#guard corpus.all fun t => BMS.kind (mat t 0) == kindA t
-- 深さ 2 の閉包でも成り立つ (`nil` に落ちた場合を除く)。
#guard corpus.all fun t => (List.range 4).all fun n =>
  let u := fs t n
  u == .nil || (List.range 4).all fun m => BMS.expand? (mat u 0) m == some (mat (fs u m) 0)

/-! ## §7 THE CLASSIFICATION — what the three supplies dispatch on

`certIn_region` splits on `BMS.kind S`, so each supply needs to know which INDEX produced a
matrix of that kind.  The answer is read straight off the index's last summand, and the
proof is one fact about `mat`: the last column of a nonempty `mat a d` sits at depth `≥ d`,
so at `d ≥ 1` it has a nonzero row-0 entry and `lnz` is never `none`.  Hence a top-level
index is a successor exactly when its last summand is `ψ₀(0)` — the one summand whose block
is the single column `(0,0)`. -/

theorem getLast?_append_ne {α : Type} : ∀ (X Z : List α), Z ≠ [] →
    (X ++ Z).getLast? = Z.getLast? := by
  intro X
  induction X with
  | nil => intro Z _; rfl
  | cons a t ih =>
    intro Z hZ
    show ((a :: (t ++ Z))).getLast? = _
    rw [List.getLast?_cons_of_ne_nil (by
      intro h
      rcases List.append_eq_nil_iff.mp h with ⟨_, h2⟩
      exact hZ h2)]
    exact ih Z hZ

/-- 空でない添字の行列の最後の列は、深さ以上の行 0 の値をもつ。 -/
theorem mat_getLast : ∀ (a : A) (d : Nat), a ≠ .nil →
    ∃ (x y : Nat), (mat a d).getLast? = some [x, y] ∧ d ≤ x := by
  intro a
  induction a with
  | nil => intro d h; exact absurd rfl h
  | om r _ =>
    intro d _
    refine ⟨d, 1, ?_, Nat.le_refl d⟩
    show (mat r d ++ [[d, 1]]).getLast? = _
    rw [getLast?_append_ne _ _ (by simp)]
    rfl
  | ps r a _ iha =>
    intro d _
    show ∃ x y, (mat r d ++ ([d, 0] :: mat a (d + 1))).getLast? = some [x, y] ∧ d ≤ x
    rw [getLast?_append_ne _ _ (by simp)]
    cases a with
    | nil =>
      refine ⟨d, 0, ?_, Nat.le_refl d⟩
      rfl
    | om b =>
      obtain ⟨x, y, hx, hd⟩ := iha (d + 1) (by intro h; exact A.noConfusion h)
      refine ⟨x, y, ?_, by omega⟩
      rw [List.getLast?_cons_of_ne_nil (by
        intro h
        rw [h] at hx
        exact absurd hx (by simp))]
      exact hx
    | ps b c =>
      obtain ⟨x, y, hx, hd⟩ := iha (d + 1) (by intro h; exact A.noConfusion h)
      refine ⟨x, y, ?_, by omega⟩
      rw [List.getLast?_cons_of_ne_nil (by
        intro h
        rw [h] at hx
        exact absurd hx (by simp))]
      exact hx

/-- **種別は添字が決める。** 最上位の添字は、最後の加数が `ψ₀(0)` のときちょうど後続。 -/
theorem kind_mat : ∀ (t : A), topOK t = true → BMS.kind (mat t 0) = kindA t := by
  intro t
  cases t with
  | nil => intro _; rfl
  | om r => intro h; exact Bool.noConfusion h
  | ps r a =>
    intro _
    cases a with
    | nil =>
      show BMS.kind (mat r 0 ++ [[0, 0]]) = BMS.Kind.succ
      show (match (mat r 0 ++ [[0, 0]]).getLast? with
        | none => BMS.Kind.zero
        | some L => match lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
        = BMS.Kind.succ
      rw [getLast?_append_ne _ _ (by simp)]
      rfl
    | om b => exact kind_mat_lim r (.om b) (by intro h; exact A.noConfusion h)
    | ps b c => exact kind_mat_lim r (.ps b c) (by intro h; exact A.noConfusion h)
where
  /-- 最後の加数が `ψ₀(0)` でなければ極限。 -/
  kind_mat_lim (r a : A) (ha : a ≠ .nil) : BMS.kind (mat (.ps r a) 0) = BMS.Kind.lim := by
    obtain ⟨x, y, hx, hd⟩ := mat_getLast a 1 ha
    show (match (mat r 0 ++ ([0, 0] :: mat a 1)).getLast? with
      | none => BMS.Kind.zero
      | some L => match lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
      = BMS.Kind.lim
    rw [getLast?_append_ne _ _ (by simp),
      List.getLast?_cons_of_ne_nil (by intro h; rw [h] at hx; exact absurd hx (by simp)), hx]
    show (match lnz ([x, y] : Col) with
      | none => BMS.Kind.succ | some _ => BMS.Kind.lim) = BMS.Kind.lim
    rw [lnz_pair]
    cases y with
    | zero => rw [if_neg (by omega), if_pos (by omega)]
    | succ _ => rw [if_pos (by omega)]

end Evidence.Region
