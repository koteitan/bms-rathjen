import BMS.Order
/-
Evidence/CmpM.lean — THE BMS ORDER IS A LINEAR ORDER

`BMS/Order.lean` defines `cmpCol`/`cmpM` and `ltB`, and proves nothing about them: the
file's job is to match yaBMS `-c`, and every consumer so far has `decide`d at a concrete
pair.  `Evidence/RegionV.lean`'s normal form is the first consumer that needs the ORDER
LAWS — its descending condition is a `cmpM` inequality, and showing the region closed
under `BMS.expand` means composing two of them.

Everything here is the ordinary lexicographic argument, done twice: once for `cmpCol` over
`List Nat`, once for `cmpM` over `List Col`.  The only input is that `compare` on `Nat` is
a linear order.

    cmpM_refl        cmpM M M = .eq
    cmpM_eq          cmpM M N = .eq → M = N
    cmpM_swap        cmpM N M = (cmpM M N).swap
    cmpM_trans       cmpM M N = .lt → cmpM N P = .lt → cmpM M P = .lt
    leM_trans        the `≠ .gt` form, which is what a normal form asks for

§4 adds the three facts about `++` that the region's closure proof needs: a common prefix
cancels, a proper prefix is strictly smaller, and extending the SMALLER side on the right
keeps it smaller provided what is appended starts below everything on the other side —
which for a matrix read as a forest means "starts at a shallower depth".
-/

namespace BMS

/-! ## §1 `compare` on `Nat` -/

theorem compare_def (a b : Nat) :
    compare a b = if a < b then Ordering.lt else if a = b then .eq else .gt := by
  simp [compare, compareOfLessAndEq]

theorem compare_self (a : Nat) : compare a a = .eq := by
  rw [compare_def, if_neg (Nat.lt_irrefl a), if_pos rfl]

theorem compare_eq_lt {a b : Nat} : compare a b = .lt ↔ a < b := by
  rw [compare_def]
  by_cases h : a < b
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    by_cases h2 : a = b
    · rw [if_pos h2]; exact ⟨fun hc => Ordering.noConfusion hc, fun hc => absurd hc h⟩
    · rw [if_neg h2]; exact ⟨fun hc => Ordering.noConfusion hc, fun hc => absurd hc h⟩

theorem compare_eq_eq {a b : Nat} : compare a b = .eq ↔ a = b := by
  rw [compare_def]
  by_cases h : a < b
  · rw [if_pos h]; exact ⟨fun hc => Ordering.noConfusion hc, fun hc => absurd hc (by omega)⟩
  · rw [if_neg h]
    by_cases h2 : a = b
    · rw [if_pos h2]; exact ⟨fun _ => h2, fun _ => rfl⟩
    · rw [if_neg h2]; exact ⟨fun hc => Ordering.noConfusion hc, fun hc => absurd hc h2⟩

theorem compare_eq_gt {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def]
  by_cases h : a < b
  · rw [if_pos h]; exact ⟨fun hc => Ordering.noConfusion hc, fun hc => absurd hc (by omega)⟩
  · rw [if_neg h]
    by_cases h2 : a = b
    · rw [if_pos h2]; exact ⟨fun hc => Ordering.noConfusion hc, fun hc => absurd hc (by omega)⟩
    · rw [if_neg h2]; exact ⟨fun _ => by omega, fun _ => rfl⟩

/-! ## §2 Columns -/

theorem cmpCol_refl : ∀ (c : Col), cmpCol c c = .eq
  | [] => rfl
  | a :: t => by
    show (compare a a).then (cmpCol t t) = .eq
    rw [compare_self, cmpCol_refl t]
    rfl

theorem cmpCol_eq : ∀ (c d : Col), cmpCol c d = .eq → c = d
  | [], [], _ => rfl
  | [], _ :: _, h => Ordering.noConfusion h
  | _ :: _, [], h => Ordering.noConfusion h
  | a :: s, b :: t, h => by
    have h' : (compare a b).then (cmpCol s t) = .eq := h
    cases hab : compare a b with
    | lt => rw [hab] at h'; exact Ordering.noConfusion h'
    | gt => rw [hab] at h'; exact Ordering.noConfusion h'
    | eq =>
      rw [hab] at h'
      rw [compare_eq_eq.mp hab, cmpCol_eq s t h']

theorem cmpCol_swap : ∀ (c d : Col), cmpCol d c = (cmpCol c d).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by
    show (compare b a).then (cmpCol t s) = ((compare a b).then (cmpCol s t)).swap
    cases hab : compare a b with
    | eq =>
      have h : a = b := compare_eq_eq.mp hab
      subst h
      rw [compare_self]
      show cmpCol t s = (cmpCol s t).swap
      exact cmpCol_swap s t
    | lt =>
      rw [show compare b a = .gt from compare_eq_gt.mpr (compare_eq_lt.mp hab)]
      rfl
    | gt =>
      rw [show compare b a = .lt from compare_eq_lt.mpr (compare_eq_gt.mp hab)]
      rfl

theorem cmpCol_trans : ∀ (c d e : Col), cmpCol c d = .lt → cmpCol d e = .lt → cmpCol c e = .lt
  | [], [], _, h, _ => Ordering.noConfusion h
  | [], _ :: _, [], _, h => Ordering.noConfusion h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => Ordering.noConfusion h
  | _ :: _, _ :: _, [], _, h => Ordering.noConfusion h
  | a :: s, b :: t, c :: u, h1, h2 => by
    have g1 : (compare a b).then (cmpCol s t) = .lt := h1
    have g2 : (compare b c).then (cmpCol t u) = .lt := h2
    show (compare a c).then (cmpCol s u) = .lt
    cases hab : compare a b with
    | gt => rw [hab] at g1; exact Ordering.noConfusion g1
    | lt =>
      have hab' : a < b := compare_eq_lt.mp hab
      cases hbc : compare b c with
      | gt => rw [hbc] at g2; exact Ordering.noConfusion g2
      | lt => rw [show compare a c = .lt from
                compare_eq_lt.mpr (Nat.lt_trans hab' (compare_eq_lt.mp hbc))]; rfl
      | eq =>
        have h : b = c := compare_eq_eq.mp hbc
        subst h
        rw [hab]
        rfl
    | eq =>
      have hab' : a = b := compare_eq_eq.mp hab
      subst hab'
      rw [compare_self] at g1
      cases hbc : compare a c with
      | gt => rw [hbc] at g2; exact Ordering.noConfusion g2
      | lt => rfl
      | eq =>
        rw [hbc] at g2
        show cmpCol s u = .lt
        exact cmpCol_trans s t u g1 g2

/-! ## §3 Matrices -/

theorem cmpM_refl : ∀ (M : Matrix), cmpM M M = .eq
  | [] => rfl
  | c :: t => by
    show (cmpCol c c).then (cmpM t t) = .eq
    rw [cmpCol_refl, cmpM_refl t]
    rfl

theorem cmpM_eq : ∀ (M N : Matrix), cmpM M N = .eq → M = N
  | [], [], _ => rfl
  | [], _ :: _, h => Ordering.noConfusion h
  | _ :: _, [], h => Ordering.noConfusion h
  | c :: s, d :: t, h => by
    have h' : (cmpCol c d).then (cmpM s t) = .eq := h
    cases hcd : cmpCol c d with
    | lt => rw [hcd] at h'; exact Ordering.noConfusion h'
    | gt => rw [hcd] at h'; exact Ordering.noConfusion h'
    | eq =>
      rw [hcd] at h'
      rw [cmpCol_eq c d hcd, cmpM_eq s t h']

theorem cmpM_swap : ∀ (M N : Matrix), cmpM N M = (cmpM M N).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | c :: s, d :: t => by
    show (cmpCol d c).then (cmpM t s) = ((cmpCol c d).then (cmpM s t)).swap
    rw [cmpCol_swap c d]
    cases hcd : cmpCol c d with
    | eq => show cmpM t s = (cmpM s t).swap
            exact cmpM_swap s t
    | lt => rfl
    | gt => rfl

theorem cmpM_trans : ∀ (M N P : Matrix), cmpM M N = .lt → cmpM N P = .lt → cmpM M P = .lt
  | [], [], _, h, _ => Ordering.noConfusion h
  | [], _ :: _, [], _, h => Ordering.noConfusion h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => Ordering.noConfusion h
  | _ :: _, _ :: _, [], _, h => Ordering.noConfusion h
  | c :: s, d :: t, e :: u, h1, h2 => by
    have g1 : (cmpCol c d).then (cmpM s t) = .lt := h1
    have g2 : (cmpCol d e).then (cmpM t u) = .lt := h2
    show (cmpCol c e).then (cmpM s u) = .lt
    cases hcd : cmpCol c d with
    | gt => rw [hcd] at g1; exact Ordering.noConfusion g1
    | lt =>
      cases hde : cmpCol d e with
      | gt => rw [hde] at g2; exact Ordering.noConfusion g2
      | lt => rw [cmpCol_trans c d e hcd hde]; rfl
      | eq =>
        have h : d = e := cmpCol_eq d e hde
        subst h
        rw [hcd]
        rfl
    | eq =>
      have h : c = d := cmpCol_eq c d hcd
      have g1' : cmpM s t = Ordering.lt := by rw [hcd] at g1; exact g1
      rw [h]
      cases hde : cmpCol d e with
      | gt => rw [hde] at g2; exact Ordering.noConfusion g2
      | lt => rfl
      | eq =>
        rw [hde] at g2
        show cmpM s u = .lt
        exact cmpM_trans s t u g1' g2

/-! ## §4 Appends

The three facts the region's closure proof needs about `cmpM` and `++`.  A common prefix
cancels; a proper prefix is strictly smaller; and extending the SMALLER side on the right
keeps it smaller as long as whatever is appended starts below everything on the other
side — which for a matrix read as a forest means "starts at a shallower depth". -/

theorem cmpM_append_left : ∀ (X Y Z : Matrix), cmpM (X ++ Y) (X ++ Z) = cmpM Y Z
  | [], _, _ => rfl
  | c :: s, Y, Z => by
    show (cmpCol c c).then (cmpM (s ++ Y) (s ++ Z)) = cmpM Y Z
    rw [cmpCol_refl, cmpM_append_left s Y Z]
    rfl

theorem cmpM_prefix_lt : ∀ (X : Matrix) (c : Col) (Y : Matrix), cmpM X (X ++ (c :: Y)) = .lt
  | [], _, _ => rfl
  | d :: s, c, Y => by
    show (cmpCol d d).then (cmpM s (s ++ (c :: Y))) = .lt
    rw [cmpCol_refl, cmpM_prefix_lt s c Y]
    rfl

/-- 小さい側を右に伸ばしても小さいまま — 伸ばす先頭が相手のどの列より小さければ。 -/
theorem cmpM_append_lt : ∀ (M N R : Matrix), cmpM M N = .lt →
    (∀ d ∈ R.head?, ∀ c ∈ N, cmpCol d c = .lt) → cmpM (M ++ R) N = .lt
  | [], [], _, h, _ => Ordering.noConfusion h
  | _ :: _, [], _, h, _ => Ordering.noConfusion h
  | [], c :: t, R, _, hg => by
    show cmpM R (c :: t) = .lt
    cases R with
    | nil => rfl
    | cons d u =>
      show (cmpCol d c).then (cmpM u t) = .lt
      rw [hg d rfl c (by simp)]
      rfl
  | m :: s, n :: t, R, h, hg => by
    have h' : (cmpCol m n).then (cmpM s t) = .lt := h
    show (cmpCol m n).then (cmpM (s ++ R) t) = .lt
    cases hmn : cmpCol m n with
    | gt => rw [hmn] at h'; exact Ordering.noConfusion h'
    | lt => rfl
    | eq =>
      rw [hmn] at h'
      show cmpM (s ++ R) t = .lt
      exact cmpM_append_lt s t R h' (fun d hd c hc => hg d hd c (List.mem_cons_of_mem n hc))

/-- **右に伸ばした側と比べたときの長さの下界。** `X > Y` かつ `X < Y ++ Z` なら、`Y` は
    `X` の真の接頭辞でしかありえないので `|Y| < |X|`。これが、標準形の不動点条件を
    接頭辞へ制限するときの唯一の非自明な段である。 -/
theorem cmpM_gt_lt_len : ∀ (X Y Z : Matrix), cmpM X Y = .gt → cmpM X (Y ++ Z) = .lt →
    Y.length < X.length
  | [], [], _, h, _ => Ordering.noConfusion h
  | [], _ :: _, _, h, _ => Ordering.noConfusion h
  | x :: s, [], _, _, _ => by simp
  | x :: s, y :: t, Z, h1, h2 => by
    have g1 : (cmpCol x y).then (cmpM s t) = .gt := h1
    have g2 : (cmpCol x y).then (cmpM s (t ++ Z)) = .lt := h2
    cases hxy : cmpCol x y with
    | gt => rw [hxy] at g2; exact Ordering.noConfusion g2
    | lt => rw [hxy] at g1; exact Ordering.noConfusion g1
    | eq =>
      rw [hxy] at g1 g2
      have := cmpM_gt_lt_len s t Z g1 g2
      show (t.length + 1) < (s.length + 1)
      omega

/-! ## §5 The `≤` form, which is what a normal form asks for -/

/-- `M ≤ N` を `cmpM M N ≠ .gt` として読む。 -/
def leM (M N : Matrix) : Bool := cmpM M N != .gt

theorem leM_refl (M : Matrix) : leM M M = true := by
  show (cmpM M M != .gt) = true
  rw [cmpM_refl]
  rfl

theorem leM_trans {M N P : Matrix} (h1 : leM M N = true) (h2 : leM N P = true) :
    leM M P = true := by
  have g1 : (cmpM M N != Ordering.gt) = true := h1
  have g2 : (cmpM N P != Ordering.gt) = true := h2
  show (cmpM M P != Ordering.gt) = true
  cases h : cmpM M P with
  | lt => rfl
  | eq => rfl
  | gt =>
    exfalso
    -- `P < M`, so one of `M ≤ N`, `N ≤ P` must break
    have hPM : cmpM P M = .lt := by
      have := cmpM_swap M P
      rw [h] at this
      exact this
    cases hMN : cmpM M N with
    | gt => rw [hMN] at g1; exact Bool.noConfusion g1
    | lt =>
      have hPN : cmpM P N = .lt := cmpM_trans P M N hPM hMN
      have : cmpM N P = .gt := by
        have := cmpM_swap P N
        rw [hPN] at this
        exact this
      rw [this] at g2; exact Bool.noConfusion g2
    | eq =>
      rw [cmpM_eq M N hMN] at hPM
      have : cmpM N P = .gt := by
        have := cmpM_swap P N
        rw [hPM] at this
        exact this
      rw [this] at g2; exact Bool.noConfusion g2

end BMS
