import Rows.G4Dict

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G4

def M : BMS.Matrix := [[0,0],[1,1],[2,2]]
def t : Term := psi (Z zero) (Z (phi zero zero))

/-- The ascending row-one tail produced by expanding `M`. -/
def A (a m : Nat) : Trans.Recal.PS :=
  (List.range m).map (fun k => (((k+a : Nat) : Int), (1 : Int)))

def P (m : Nat) : Trans.Recal.PS := (0,0) :: (1,1) :: A 2 m

/-- The one-pair-at-a-time ladder, including the reader's singleton base. -/
def L : Nat → Trans.Recal.PS
  | 0 => [(0,0)]
  | m+1 => P m

def rep1 : Nat → Trans.Dict.BT
  | 0 => .zero
  | m+1 => .D 1 (rep1 m)

def PBT (m : Nat) : Trans.Dict.BT := .D 0 (rep1 (m+1))

def LBT : Nat → Trans.Dict.BT
  | 0 => .zero
  | m+1 => PBT m

/-- A positive row-one head followed by an ascending row-one tail. -/
def K (d a m : Nat) : Trans.Recal.PS :=
  (((d : Nat) : Int), (1 : Int)) :: A a m

/-- The same family below the zero root used by principal reduction. -/
def C (d a m : Nat) : Trans.Recal.PS := (0,0) :: K d a m

theorem A_succ_last (a m : Nat) :
    A a (m+1) = A a m ++ [((((a+m : Nat) : Int), (1 : Int)))] := by
  unfold A
  rw [List.range_succ, List.map_append]
  simp [Nat.add_comm]

theorem A_succ (a m : Nat) :
    A a (m+1) = (((a : Nat) : Int), (1 : Int)) :: A (a+1) m := by
  unfold A
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro k _
    apply Prod.ext <;> simp
    push_cast
    omega

theorem length_A (a m : Nat) : (A a m).length = m := by
  simp [A]

theorem lenI_A (a m : Nat) : Trans.Recal.lenI (A a m) = (m : Int) := by
  unfold Trans.Recal.lenI
  rw [length_A]

theorem getD_A (a m i : Nat) (h : i < m) :
    (A a m).getD i (0,0) = ((((i+a : Nat) : Int), (1 : Int))) := by
  unfold A
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem gp0_A (a m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.gp0 (A a m) j = (a : Int) + j := by
  show (if j < 0 then 0 else ((A a m).getD j.toNat (0,0)).1) = _
  rw [if_neg (by omega), getD_A a m j.toNat (by omega)]
  push_cast
  omega

theorem gp1_A (a m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.gp1 (A a m) j = 1 := by
  show (if j < 0 then 0 else ((A a m).getD j.toNat (0,0)).2) = 1
  rw [if_neg (by omega), getD_A a m j.toNat (by omega)]

theorem fpar0_A_zero (a m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.fpar0 (A a m) 0 0 = -1 := by
  show (if (0 : Int) < 0 ∨ (0 : Int) ≥ Trans.Recal.lenI (A a m) then -1
        else Trans.Recal.fpar0Aux ((A a m).length + 1) (A a m)
          (Trans.Recal.gp0 (A a m) 0) (-1) 0) = -1
  rw [if_neg (by rw [lenI_A]; omega), length_A]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar0Aux]
    rw [if_pos (by omega)]

theorem fpar_A (a m k : Nat) (hk0 : 0 < k) (hk : k < m) :
    Trans.Recal.fpar (A a m) 0 (k : Int) 0 = ((k-1 : Nat) : Int) := by
  show (if (k : Int) < 0 ∨ (k : Int) ≥ Trans.Recal.lenI (A a m) then -1
        else if (0 : Nat) == 0 then
          Trans.Recal.fpar0Aux ((A a m).length + 1) (A a m)
            (Trans.Recal.gp0 (A a m) (k : Int)) ((k : Int) - 1) 0
        else _) = _
  rw [if_neg (by rw [lenI_A]; omega)]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  rw [gp0_A a m (k : Int) (by omega) (by omega), length_A]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar0Aux]
    rw [if_neg (by omega), gp0_A a (p+1) ((k : Int)-1) (by omega) (by omega),
      if_pos (by omega)]
    omega

theorem fpar_A_zero (a m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.fpar (A a m) 0 0 0 = -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A]; omega), if_pos (by rfl)]
  have h := fpar0_A_zero a m hm
  unfold Trans.Recal.fpar0 at h
  rw [if_neg (by rw [lenI_A]; omega)] at h
  exact h

theorem isAncAux_A (a m k : Nat) : ∀ f : Nat, k < m → k < f →
    Trans.Recal.isAncAux f (A a m) 0 (k : Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m → k < f →
    Trans.Recal.isAncAux f (A a m) 0 (k : Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k = 0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int) == (k:Int)) = false from
          beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_A a m k (by omega) hkm]
      rw [show ((((k-1 : Nat) : Int)) == (-1:Int)) = false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_A (a m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.isPrincipalP (A a m) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (A a m) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_A]
        cases m with
        | zero => omega
        | succ q =>
          rw [gp1_A a (q+1) 0 (by omega) (by omega)]
          cases q <;> rfl,
      lenI_A]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_A]; omega), length_A]
  simp only [Bool.not_false, Bool.true_and]
  rw [show (m:Int)-1=((m-1:Nat):Int) by omega]
  exact isAncAux_A a m (m-1) (m+1) (by omega) (by omega)

theorem fAncAux_A_last (a m k : Nat) : ∀ (f : Nat) (acc : List Int),
    k < m → k < f → acc.getLast? = some (k : Int) →
    (Trans.Recal.fAncAux f (A a m) 0 (k : Int) 0 acc).getLast? = some 0 := by
  refine Nat.strongRecOn (motive := fun k => ∀ (f : Nat) (acc : List Int),
    k < m → k < f → acc.getLast? = some (k : Int) →
    (Trans.Recal.fAncAux f (A a m) 0 (k : Int) 0 acc).getLast? = some 0) k ?_
  intro k ih f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0 : k = 0
    · subst k
      rw [show Trans.Recal.fpar (A a m) 0 ((0:Nat):Int) 0 = -1 from by
        simpa using fpar_A_zero a m (by omega), if_neg (by omega)]
      exact hlast
    · rw [fpar_A a m k (by omega) hkm, if_pos (by omega)]
      exact ih (k-1) (by omega) f (acc ++ [((k-1:Nat):Int)])
        (by omega) (by omega) (by simp)

theorem fAnc_A_last (a m : Nat) (hm : 1 ≤ m) :
    (Trans.Recal.fAnc (A a m) 0 ((m-1:Nat):Int) 0).getLast? = some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_A]; omega), length_A]
  exact fAncAux_A_last a m (m-1) (m+1) [((m-1:Nat):Int)]
    (by omega) (by omega) (by simp)

theorem slice_A_full (a m : Nat) :
    Trans.Recal.slice (A a m) 0 (m : Int) = A a m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero, List.drop_zero]
  rw [show ((m:Int)-0).toNat = m by omega]
  simpa only [length_A] using
    (List.take_length : (A a m).take (A a m).length = A a m)

theorem ppair_A (a m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.ppair (A a m) = [A a m] := by
  cases m with
  | zero => omega
  | succ p =>
    unfold Trans.Recal.ppair
    rw [length_A, lenI_A]
    simp only [Trans.Recal.ppairAux]
    rw [if_neg (by omega), show ((p+1:Nat):Int)-1 = (p:Int) by omega]
    have hlast := fAnc_A_last a (p+1) (by omega)
    rw [show p+1-1 = p by omega] at hlast
    rw [hlast]
    simp only [Option.getD_some]
    rw [show (p:Int)+1 = ((p+1:Nat):Int) by omega, slice_A_full]
    rw [if_pos (by omega)]

theorem derp_A (a m : Nat) : Trans.Recal.derp (A a (m+1)) = A (a+1) m := by
  rw [A_succ]
  rfl

theorem incrFirst_A (a d m : Nat) :
    Trans.Recal.incrFirst (A a m) (d : Int) = A (a+d) m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext <;> simp
  push_cast
  omega

theorem incrFirst_K (d a m : Nat) :
    Trans.Recal.incrFirst (K d a m) 1 = K (d+1) (a+1) m := by
  unfold Trans.Recal.incrFirst K
  rw [List.map_cons]
  rw [show (A a m).map (fun c => (c.1+1,c.2)) = A (a+1) m from by
    simpa [Trans.Recal.incrFirst] using incrFirst_A a 1 m]
  push_cast
  congr 1

theorem length_K (d a m : Nat) : (K d a m).length = m+1 := by
  simp [K, length_A]

theorem lenI_K (d a m : Nat) : Trans.Recal.lenI (K d a m) = (m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_K]
  omega

theorem gp0_K_zero (d a m : Nat) : Trans.Recal.gp0 (K d a m) 0 = (d:Int) := by
  rfl

theorem gp1_K (d a m k : Nat) (hk : k < m+1) :
    Trans.Recal.gp1 (K d a m) (k:Int) = 1 := by
  cases k with
  | zero => rfl
  | succ k =>
    show (if ((k+1:Nat):Int)<0 then 0 else ((K d a m).getD (k+1) (0,0)).2) = 1
    rw [if_neg (by omega)]
    show ((A a m).getD k (0,0)).2 = 1
    rw [getD_A a m k (by omega)]

theorem gp0_K_pos (d a m k : Nat) (hk : k < m) :
    Trans.Recal.gp0 (K d a m) ((k+1:Nat):Int) = (a:Int)+(k:Int) := by
  show (if ((k+1:Nat):Int)<0 then 0 else ((K d a m).getD (k+1) (0,0)).1) = _
  rw [if_neg (by omega)]
  show ((A a m).getD k (0,0)).1 = _
  rw [getD_A a m k hk]
  push_cast
  omega

theorem fpar_K (d a m k : Nat) (hda : d < a) (hk0 : 0 < k) (hk : k < m+1) :
    Trans.Recal.fpar (K d a m) 0 (k:Int) 0 = ((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_K]; omega), if_pos (by rfl), length_K]
  obtain ⟨q, rfl⟩ : ∃ q : Nat, k=q+1 := ⟨k-1, by omega⟩
  rw [gp0_K_pos d a m q (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega)]
  cases q with
  | zero =>
    rw [show (((0+1:Nat):Int)-1)=0 by omega, gp0_K_zero,
      if_pos (by push_cast; omega)]
    omega
  | succ q =>
    rw [show ((q+1+1:Nat):Int)-1=((q+1:Nat):Int) by omega,
      gp0_K_pos d a m q (by omega), if_pos (by push_cast; omega)]
    omega

theorem isAncAux_K (d a m k : Nat) (hda : d < a) : ∀ f : Nat,
    k < m+1 → k < f → Trans.Recal.isAncAux f (K d a m) 0 (k:Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m+1 → k < f →
    Trans.Recal.isAncAux f (K d a m) 0 (k:Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_K d a m k hda (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_K (d a m : Nat) (hda : d < a) :
    Trans.Recal.isPrincipalP (K d a m) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (K d a m) = false from by
        show ((K d a m).length == 1 &&
          (Trans.Recal.gp1 (K d a m) 0 == 0)) = false
        rw [length_K, show Trans.Recal.gp1 (K d a m) 0 = 1 from
          gp1_K d a m 0 (by omega)]
        cases m <;> rfl,
      lenI_K]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_K]; omega), length_K]
  simp only [Bool.not_false, Bool.true_and]
  rw [show (m:Int)+1-1=(m:Int) by omega]
  exact isAncAux_K d a m m hda (m+2) (by omega) (by omega)

theorem length_C (d a m : Nat) : (C d a m).length = m+2 := by
  simp [C, length_K]

theorem lenI_C (d a m : Nat) : Trans.Recal.lenI (C d a m) = (m:Int)+2 := by
  unfold Trans.Recal.lenI
  rw [length_C]
  omega

theorem gp0_C_zero (d a m : Nat) : Trans.Recal.gp0 (C d a m) 0 = 0 := rfl

theorem gp0_C_one (d a m : Nat) : Trans.Recal.gp0 (C d a m) 1 = (d:Int) := by
  rfl

theorem gp0_C_tail (d a m q : Nat) (hq : q < m) :
    Trans.Recal.gp0 (C d a m) ((q+2:Nat):Int) = (a:Int)+(q:Int) := by
  show Trans.Recal.gp0 (K d a m) ((q+1:Nat):Int) = _
  exact gp0_K_pos d a m q hq

theorem gp1_C_zero (d a m : Nat) : Trans.Recal.gp1 (C d a m) 0 = 0 := rfl

theorem gp1_C_pos (d a m k : Nat) (hk0 : 0 < k) (hk : k < m+2) :
    Trans.Recal.gp1 (C d a m) (k:Int) = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q : Nat, k=q+1 := ⟨k-1, by omega⟩
  show Trans.Recal.gp1 (K d a m) (q:Int) = 1
  exact gp1_K d a m q (by omega)

theorem fpar_C (d a m k : Nat) (hd : 0 < d) (hda : d < a)
    (hk0 : 0 < k) (hk : k < m+2) :
    Trans.Recal.fpar (C d a m) 0 (k:Int) 0 = ((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega), if_pos (by rfl), length_C]
  obtain ⟨q, rfl⟩ : ∃ q : Nat, k=q+1 := ⟨k-1, by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega)]
  cases q with
  | zero =>
    rw [show ((0+1:Nat):Int)=1 by omega,
      gp0_C_one,
      show (1:Int)-1=0 by omega,
      gp0_C_zero,
      if_pos (by push_cast; omega)]
    omega
  | succ q =>
    rw [show ((q+1+1:Nat):Int)=((q+2:Nat):Int) by omega,
      gp0_C_tail d a m q (by omega)]
    rw [show ((q+2:Nat):Int)-1=((q+1:Nat):Int) by omega]
    cases q with
    | zero =>
      rw [show ((0+1:Nat):Int)=1 by omega, gp0_C_one,
        if_pos (by push_cast; omega)]
    | succ q =>
      rw [show ((q+1+1:Nat):Int)=((q+2:Nat):Int) by omega,
        gp0_C_tail d a m q (by omega),
        if_pos (by push_cast; omega)]
      omega

theorem fpar0_C_adj (d a m k : Nat) (hd : 0<d) (hda : d<a)
    (hk0 : 0<k) (hk : k<m+2) :
    Trans.Recal.fpar0 (C d a m) (k:Int) ((k-1:Nat):Int)=((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_C]; omega), length_C]
  obtain ⟨q,rfl⟩ : ∃ q:Nat,k=q+1 := ⟨k-1,by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega)]
  cases q with
  | zero =>
    rw [show ((0+1:Nat):Int)=1 by omega,
      show ((0+1-1:Nat):Int)=0 by omega, gp0_C_one,
      show (1:Int)-1=0 by omega, gp0_C_zero,
      if_pos (by push_cast; omega)]
  | succ q =>
    rw [show Trans.Recal.gp0 (C d a m) ((q+2:Nat):Int)=(a:Int)+(q:Int) from
          gp0_C_tail d a m q (by omega)]
    rw [show ((q+2:Nat):Int)-1=((q+1:Nat):Int) by omega]
    cases q with
    | zero =>
      rw [show ((0+1:Nat):Int)=1 by omega, gp0_C_one,
        if_pos (by push_cast; omega)]
    | succ q =>
      rw [show Trans.Recal.gp0 (C d a m) ((q+2:Nat):Int)=(a:Int)+(q:Int) from
            gp0_C_tail d a m q (by omega),
        if_pos (by push_cast; omega)]
      omega

theorem isAncAux_C (d a m k : Nat) (hd : 0 < d) (hda : d < a) : ∀ f : Nat,
    k < m+2 → k < f → Trans.Recal.isAncAux f (C d a m) 0 (k:Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m+2 → k < f →
    Trans.Recal.isAncAux f (C d a m) 0 (k:Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_C d a m k hd hda (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_C (d a m : Nat) (hd : 0 < d) (hda : d < a) :
    Trans.Recal.isPrincipalP (C d a m) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (C d a m) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_C]
        simp,
      lenI_C]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_C]; omega), length_C]
  simp only [Bool.not_false, Bool.true_and]
  rw [show (m:Int)+2-1=((m+1:Nat):Int) by omega]
  exact isAncAux_C d a m (m+1) hd hda (m+3) (by omega) (by omega)

theorem fpar0_C_one (d a m : Nat) (hd : 0 < d) :
    Trans.Recal.fpar0 (C d a m) 1 0 = 0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_C]; omega), length_C, gp0_C_one]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (1:Int)-1=0 by omega, gp0_C_zero,
    if_pos (by push_cast; omega)]

theorem fpar0_C_two (d a m : Nat) (hda : d < a) (hm : 1 ≤ m) :
    Trans.Recal.fpar0 (C d a m) 2 1 = 1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_C]; omega), length_C,
    show Trans.Recal.gp0 (C d a m) 2=(a:Int) from by
      simpa using gp0_C_tail d a m 0 (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (2:Int)-1=1 by omega, gp0_C_one,
    if_pos (by push_cast; omega)]

theorem fpar0_C_one_lb (d a m : Nat) :
    Trans.Recal.fpar0 (C d a m) 1 1 = -1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_C]; omega), length_C]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_C_one (d a m : Nat) (hd : 0 < d) :
    Trans.Recal.fpar (C d a m) 1 1 0 = 0 := by
  have hgp : Trans.Recal.gp1 (C d a m) 1 = 1 := by
    simpa using gp1_C_pos d a m 1 (by omega) (by omega)
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [length_C, hgp]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_C_one d a m hd, if_neg (by omega), gp1_C_zero,
    if_pos (by omega)]

theorem fpar1_C_two_lb (d a m : Nat) (hda : d < a) (hm : 1 ≤ m) :
    Trans.Recal.fpar (C d a m) 1 2 1 = -1 := by
  have hgp2 : Trans.Recal.gp1 (C d a m) 2 = 1 := by
    simpa using gp1_C_pos d a m 2 (by omega) (by omega)
  have hgp1 : Trans.Recal.gp1 (C d a m) 1 = 1 := by
    simpa using gp1_C_pos d a m 1 (by omega) (by omega)
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [hgp2, length_C]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_C_two d a m hda hm, if_neg (by omega),
    hgp1, if_neg (by omega)]
  rw [fpar0_C_one_lb, if_pos (by omega)]

theorem fpar1_C_two (d a m : Nat) (hd : 0 < d) (hda : d < a) (hm : 1 ≤ m) :
    Trans.Recal.fpar (C d a m) 1 2 0 = 0 := by
  have hgp2 : Trans.Recal.gp1 (C d a m) 2 = 1 := by
    simpa using gp1_C_pos d a m 2 (by omega) (by omega)
  have hgp1 : Trans.Recal.gp1 (C d a m) 1 = 1 := by
    simpa using gp1_C_pos d a m 1 (by omega) (by omega)
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [hgp2, length_C]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (C d a m) 2 0=1 from by
        have h := fpar_C d a m 2 hd hda (by omega) (by omega)
        simpa using h,
    if_neg (by omega), hgp1, if_neg (by omega)]
  rw [fpar0_C_one d a m hd, if_neg (by omega), gp1_C_zero, if_pos (by omega)]

theorem isParentP_C_one (d a m : Nat) (hd : 0 < d) :
    Trans.Recal.isParentP (C d a m) 1 1 0 = true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_C_one d a m hd, lenI_C]
  rw [show decide ((0:Int)<(m:Int)+2)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_C_two (d a m : Nat) (hda : d < a) (hm : 1 ≤ m) :
    Trans.Recal.isParentP (C d a m) 1 2 1 = false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_C_two_lb d a m hda hm]
  simp

theorem trMax_C (d a m : Nat) (hd : 0 < d) (hda : d < a) :
    Trans.Recal.trMax (C d a m) = 1 := by
  show Trans.Recal.trMaxAux ((C d a m).length+1) (C d a m) 0 = 1
  rw [length_C]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_C]; omega),
    show Trans.Recal.isParentP (C d a m) 1 (0+1) 0 = true from by
      simpa using isParentP_C_one d a m hd]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [if_neg (by rw [lenI_C]; omega)]
  cases m with
  | zero =>
    rw [if_pos (by rfl)]
    omega
  | succ p =>
    rw [show Trans.Recal.isParentP (C d a (p+1)) 1 (0+1+1) (0+1) = false from by
      simpa using isParentP_C_two d a (p+1) hda (by omega), if_pos (by rfl)]
    omega

theorem brF_C_succ (d a m : Nat) (hd : 0 < d) (hda : d < a) :
    Trans.Recal.brF (C d a (m+1)) = [A a (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_C d a (m+1) hd hda]
  show Trans.Recal.ppair (A a (m+1)) = [A a (m+1)]
  exact ppair_A a (m+1) (by omega)

theorem firstNodes_C_succ (d a m : Nat) (hd : 0 < d) (hda : d < a) :
    Trans.Recal.firstNodes (C d a (m+1)) = [2, ((m+3:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_C_succ d a m hd hda, trMax_C d a (m+1) hd hda]
  simp [length_A]
  omega

theorem joints_C_succ (d a m : Nat) (hd : 0 < d) (hda : d < a) :
    Trans.Recal.joints (C d a (m+1)) = [1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_C_succ d a m hd hda]
  change [Trans.Recal.fpar (C d a (m+1)) 0 2 0] = [1]
  rw [show Trans.Recal.fpar (C d a (m+1)) 0 2 0 = 1 from by
    have h := fpar_C d a (m+1) 2 hd hda (by omega) (by omega)
    simpa using h]

theorem red_C_zero (d a f : Nat) (hd : 0 < d) (hda : d < a) :
    Trans.Recal.red (f+1) (C d a 0) = ([(0,0),(1,1)] : Trans.Recal.PS) := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C d a 0) = false from by rfl,
    isPrincipalP_C d a 0 hd hda]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (C d a 0) 0 == 0 &&
      Trans.Recal.gp1 (C d a 0) 0 == 0) = true from rfl]
  simp only [if_true]
  rw [trMax_C d a 0 hd hda, lenI_C]
  rw [show ((1:Int)==(((0:Nat):Int)+2-1))=true from by decide]
  rfl

theorem red_K_zero (d a f : Nat) (hd : 0 < d) (hda : d < a) :
    Trans.Recal.red (f+2) (K d a 0) = A 1 1 := by
  have hgp1 : Trans.Recal.gp1 (K d a 0) 0 = 1 := rfl
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d a 0) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_K, hgp1]
        rfl,
      isPrincipalP_K d a 0 hda]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (K d a 0) 0 == 0 &&
      Trans.Recal.gp1 (K d a 0) 0 == 0) = false from by
        rw [gp0_K_zero, hgp1]
        simp]
  simp only [Bool.false_eq_true, if_false]
  rw [show (Trans.Recal.gp1 (K d a 0) 0 == 0) = false from by
        rw [hgp1]
        rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show Trans.Recal.jjSeq 0 (Trans.Recal.gp1 (K d a 0) 0 - 1) ++
      Trans.Recal.incrFirst (K d a 0) (Trans.Recal.gp1 (K d a 0) 0) =
      C (d+1) (a+1) 0 from by
        rw [hgp1, incrFirst_K]
        rfl,
    red_C_zero (d+1) (a+1) f (by omega) (by omega)]
  simp only [Trans.Recal.lenI]
  rw [hgp1]
  rw [if_pos (by decide)]
  rfl

theorem red_C_step (d a m f : Nat) (hd : 0 < d) (hda : d < a)
    (hK : Trans.Recal.red (2*m+f+2) (K 2 (a+1) m) = A 1 (m+1)) :
    Trans.Recal.red (2*(m+1)+f+1) (C d a (m+1)) =
      (0,0) :: A 1 (m+2) := by
  rw [show 2*(m+1)+f+1=(2*m+f+2)+1 by omega, Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C d a (m+1)) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_C]
        simp,
      isPrincipalP_C d a (m+1) hd hda]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (C d a (m+1)) 0 == 0 &&
      Trans.Recal.gp1 (C d a (m+1)) 0 == 0) = true from rfl]
  simp only [if_true]
  rw [trMax_C d a (m+1) hd hda, lenI_C]
  rw [show ((1:Int)==(((m+1:Nat):Int)+2-1))=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true, if_false]
  rw [brF_C_succ d a m hd hda, firstNodes_C_succ d a m hd hda,
    joints_C_succ d a m hd hda]
  simp only [List.length_cons, List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show ([A a (m+1)] : List Trans.Recal.PS).getD 0 []=A a (m+1) from rfl,
    show ([2,((m+3:Nat):Int)] : List Int).getD 0 0=2 from rfl,
    show ([1] : List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (A a (m+1)) 0=1 from
    gp1_A a (m+1) 0 (by omega) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [fpar1_C_two d a (m+1) hd hda (by omega)]
  change Trans.Recal.jjSeq 0 1 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (2*m+f+2)
      (((2:Int),(1:Int)) :: Trans.Recal.derp (A a (m+1)))) 1 = _
  rw [derp_A]
  change Trans.Recal.jjSeq 0 1 ++
    Trans.Recal.incrFirst (Trans.Recal.red (2*m+f+2) (K 2 (a+1) m)) 1 = _
  rw [hK]
  rw [show Trans.Recal.incrFirst (A 1 (m+1)) 1=A 2 (m+1) from by
    simpa using incrFirst_A 1 1 (m+1)]
  rw [show A 1 (m+2)=((1:Int),(1:Int))::A 2 (m+1) from by
    rw [show m+2=(m+1)+1 by omega, A_succ]
    rfl]
  rfl

theorem red_K_step (d a m f : Nat) (hd : 0 < d) (hda : d < a)
    (hC : Trans.Recal.red (2*(m+1)+f+1) (C (d+1) (a+1) (m+1)) =
      (0,0) :: A 1 (m+2)) :
    Trans.Recal.red (2*(m+1)+f+2) (K d a (m+1)) = A 1 (m+2) := by
  have hgp1 : Trans.Recal.gp1 (K d a (m+1)) 0=1 := by
    exact gp1_K d a (m+1) 0 (by omega)
  rw [show 2*(m+1)+f+2=(2*(m+1)+f+1)+1 by omega, Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d a (m+1))=false from by
        unfold Trans.Recal.isZeroP
        rw [length_K]
        simp,
      isPrincipalP_K d a (m+1) hda]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (K d a (m+1)) 0==0 &&
      Trans.Recal.gp1 (K d a (m+1)) 0==0)=false from by
        rw [gp0_K_zero, hgp1]
        rw [show ((d:Int)==0)=false from beq_eq_false_iff_ne.mpr (by omega)]
        rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show (Trans.Recal.gp1 (K d a (m+1)) 0==0)=false from by
        rw [hgp1]
        rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show Trans.Recal.jjSeq 0 (Trans.Recal.gp1 (K d a (m+1)) 0-1) ++
      Trans.Recal.incrFirst (K d a (m+1)) (Trans.Recal.gp1 (K d a (m+1)) 0) =
      C (d+1) (a+1) (m+1) from by
        rw [hgp1, incrFirst_K]
        rfl,
    hC]
  rw [show Trans.Recal.lenI ((0,0)::A 1 (m+2))-1=((m+2:Nat):Int) from by
        unfold Trans.Recal.lenI
        simp [length_A]]
  rw [hgp1]
  rw [show decide ((1:Int)≤((m+2:Nat):Int))=true from decide_eq_true (by omega)]
  rw [show ((0,0)::A 1 (m+2)).drop (1:Int).toNat=A 1 (m+2) from rfl,
    isPrincipalP_A 1 (m+2) (by omega)]
  simp only [Bool.true_and, if_true]
  rw [show -Trans.Recal.gp0 ((0,0)::A 1 (m+2)) 1+
      Trans.Recal.gp1 ((0,0)::A 1 (m+2)) 1=0 from by
        simp [Trans.Recal.gp0, Trans.Recal.gp1, A]]
  simp [Trans.Recal.incrFirst]

theorem red_K_C : ∀ m : Nat,
    (∀ (d a f : Nat), 0<d → d<a →
      Trans.Recal.red (2*m+f+2) (K d a m)=A 1 (m+1)) ∧
    (∀ (d a f : Nat), 0<d → d<a →
      Trans.Recal.red (2*m+f+1) (C d a m)=(0,0)::A 1 (m+1))
  | 0 => by
    constructor
    · intro d a f hd hda
      simpa using red_K_zero d a f hd hda
    · intro d a f hd hda
      simpa using red_C_zero d a f hd hda
  | m+1 => by
    have ih := red_K_C m
    have hc : ∀ (d a f : Nat), 0<d → d<a →
        Trans.Recal.red (2*(m+1)+f+1) (C d a (m+1))=
          (0,0)::A 1 (m+2) := by
      intro d a f hd hda
      apply red_C_step d a m f hd hda
      exact ih.1 2 (a+1) f (by omega) (by omega)
    constructor
    · intro d a f hd hda
      exact red_K_step d a m f hd hda
        (hc (d+1) (a+1) f (by omega) (by omega))
    · exact hc

theorem red_K_all (d a m f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (2*m+f+2) (K d a m)=A 1 (m+1) :=
  (red_K_C m).1 d a f hd hda

theorem red_C_all (d a m f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (2*m+f+1) (C d a m)=(0,0)::A 1 (m+1) :=
  (red_K_C m).2 d a f hd hda

theorem length_P (m : Nat) : (P m).length=m+2 := by
  simp [P, length_A]

theorem P_eq_C (m : Nat) : P m=C 1 2 m := rfl

theorem C_normal_eq_P (m : Nat) : (0,0)::A 1 (m+1)=P m := by
  rw [A_succ]
  rfl

theorem redP_P (m : Nat) : Trans.Recal.redP (P m)=P m := by
  have hb : 2*m+1 ≤ Trans.Recal.redFuel (P m) := by
    unfold Trans.Recal.redFuel
    rw [length_P]
    omega
  have he : Trans.Recal.redFuel (P m)=
      2*m+(Trans.Recal.redFuel (P m)-2*m-1)+1 := by omega
  unfold Trans.Recal.redP
  rw [he]
  conv => lhs; rw [P_eq_C]
  rw [red_C_all 1 2 m _ (by omega) (by omega), C_normal_eq_P]

theorem length_L (m : Nat) : (L m).length=m+1 := by
  cases m with
  | zero => rfl
  | succ m => simp [L, length_P]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  cases m with
  | zero => rfl
  | succ m => simpa [L] using redP_P m

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  exact G1.beq_PS_self (L m)

theorem isPrincipalP_P (m : Nat) : Trans.Recal.isPrincipalP (P m)=true := by
  rw [P_eq_C]
  exact isPrincipalP_C 1 2 m (by omega) (by omega)

theorem fpar_P_top (m : Nat) :
    Trans.Recal.fpar (P m) 0 ((m:Int)+1) 0=(m:Int) := by
  rw [P_eq_C]
  have h := fpar_C 1 2 m (m+1) (by omega) (by omega) (by omega) (by omega)
  simpa only [show (((m+1:Nat):Int))=(m:Int)+1 by omega,
    show (((m+1-1:Nat):Int))=(m:Int) by omega] using h

theorem fpar0_P_top_lb (m : Nat) :
    Trans.Recal.fpar0 (P m) ((m:Int)+1) (m:Int)=(m:Int) := by
  rw [P_eq_C]
  have h := fpar0_C_adj 1 2 m (m+1) (by omega) (by omega) (by omega) (by omega)
  simpa only [show (((m+1:Nat):Int))=(m:Int)+1 by omega,
    show (((m+1-1:Nat):Int))=(m:Int) by omega] using h

theorem fpar0_P_prev_lb (m : Nat) :
    Trans.Recal.fpar0 (P m) (m:Int) (m:Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [show Trans.Recal.lenI (P m)=(m:Int)+2 from by
    unfold Trans.Recal.lenI; rw [length_P]; omega]; omega), length_P]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem gp1_P_pos (m : Nat) (j : Int) (hj0 : 1≤j) (hj : j<(m:Int)+2) :
    Trans.Recal.gp1 (P m) j=1 := by
  rw [P_eq_C]
  obtain ⟨k,hk⟩ : ∃ k:Nat,j=(k:Int) := ⟨j.toNat, by omega⟩
  subst hk
  exact gp1_C_pos 1 2 m k (by omega) (by omega)

theorem fpar1_P_top_lb (m : Nat) :
    Trans.Recal.fpar (P (m+1)) 1 ((m:Int)+2) ((m:Int)+1)=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [show Trans.Recal.lenI (P (m+1))=(m:Int)+3 from by
    unfold Trans.Recal.lenI; rw [length_P]; omega]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_P_pos (m+1) ((m:Int)+2) (by omega) (by omega), length_P]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (P (m+1)) ((m:Int)+2) ((m:Int)+1)=((m:Int)+1) from by
        simpa only [show (((m+1:Nat):Int))=(m:Int)+1 by omega,
          show (((m+1:Int)+1))=(m:Int)+2 by omega] using fpar0_P_top_lb (m+1),
    if_neg (by omega),
    gp1_P_pos (m+1) ((m:Int)+1) (by omega) (by omega), if_neg (by omega)]
  rw [show Trans.Recal.fpar0 (P (m+1)) ((m:Int)+1) ((m:Int)+1)=-1 from by
        simpa only [show (((m+1:Nat):Int))=(m:Int)+1 by omega] using
          fpar0_P_prev_lb (m+1),
    if_pos (by omega)]

theorem isAdm_P_topParent_succ (m : Nat) :
    Trans.Recal.isAdm (P (m+1)) ((m:Int)+1)=true := by
  have hp : Trans.Recal.isParentP (P (m+1)) 1
      ((m:Int)+1+1) ((m:Int)+1)=false := by
    have h : Trans.Recal.isParentP (P (m+1)) 1
        ((m:Int)+2) ((m:Int)+1)=false := by
      unfold Trans.Recal.isParentP
      rw [fpar1_P_top_lb]
      rw [show (((m:Int)+1)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      rw [Bool.and_false]
    rw [show (m:Int)+1+1=(m:Int)+2 by omega]
    exact h
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide ((m:Int)+1>Trans.Recal.lenI (P (m+1)))=false from by
    apply decide_eq_false
    rw [show Trans.Recal.lenI (P (m+1))=(m:Int)+3 from by
      unfold Trans.Recal.lenI; rw [length_P]; omega]
    omega]
  simp only [Bool.false_or]
  rw [hp]
  rw [Bool.and_false]
  rfl

theorem adm_P_topParent (m : Nat) : Trans.Recal.adm (P m) (m:Int)=(m:Int) := by
  cases m with
  | zero => rfl
  | succ m =>
    unfold Trans.Recal.adm
    rw [length_P]
    simp only [Trans.Recal.admAux]
    rw [if_neg (by omega)]
    rw [show Trans.Recal.isAdm (P (m+1)) ((m+1:Nat):Int)=true from by
      simpa only [show (((m+1:Nat):Int))=(m:Int)+1 by omega] using
        isAdm_P_topParent_succ m]
    rw [if_pos rfl]

theorem transType_P_succ (m : Nat) :
    Trans.Recal.transTypeMain (P (m+1)) ((m:Int)+1) ((m:Int)+2)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_P_pos (m+1) ((m:Int)+2) (by omega) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_P_pos (m+1) ((m:Int)+1) (by omega) (by omega), if_pos (by omega),
    isAdm_P_topParent_succ m, if_pos rfl]

abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev High : Trans.Dict.BT := .D 1 D1z

theorem mkC2_P_succ (m : Nat) :
    Trans.Recal.mkC2 (P (m+1)) ((m:Int)+1) ((m:Int)+2) 3 D1z=High := by
  show Trans.Dict.BT.D 1 (Trans.Recal.bplus .zero
    (.D (Trans.Recal.gp1 (P (m+1)) ((m:Int)+2)).toNat .zero))=High
  rw [gp1_P_pos (m+1) ((m:Int)+2) (by omega) (by omega)]
  rfl

theorem size_rep1 : ∀ m, (rep1 m).size=m+1
  | 0 => rfl
  | m+1 => by rw [rep1, Trans.Dict.BT.size, size_rep1 m]; omega

theorem size_LBT_succ (m : Nat) : (LBT (m+1)).size=m+3 := by
  rw [LBT, PBT, Trans.Dict.BT.size, size_rep1]
  omega

theorem repl_rep1 : ∀ (f m : Nat), m+1≤f →
    Trans.Recal.replMark f (rep1 (m+1)) D1z High=some (rep1 (m+2))
  | 0, _, h => absurd h (by omega)
  | f+1, 0, _ => by
    rw [rep1]
    rw [show rep1 0=.zero from rfl, show rep1 (0+2)=High from rfl]
    simp only [Trans.Recal.replMark]
    rw [if_pos (G1.beq_BT_self D1z)]
  | f+1, m+1, h => by
    rw [rep1]
    show (if (Trans.Dict.BT.D 1 (rep1 (m+1)))==D1z then some High
      else (Trans.Recal.replMark f (rep1 (m+1)) D1z High).map
        (fun q => Trans.Dict.BT.D 1 q))=some (rep1 (m+1+2))
    rw [show ((Trans.Dict.BT.D 1 (rep1 (m+1)))==D1z)=false from by
      cases m <;> rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [repl_rep1 f m (by omega)]
    rfl

theorem repl_LBT (f m : Nat) (hf : m+2≤f) :
    Trans.Recal.replMark f (LBT (m+1)) D1z High=some (LBT (m+2)) := by
  cases f with
  | zero => omega
  | succ f =>
    rw [LBT, PBT]
    show (if (Trans.Dict.BT.D 0 (rep1 (m+1)))==D1z then some High
      else (Trans.Recal.replMark f (rep1 (m+1)) D1z High).map
        (fun q => Trans.Dict.BT.D 0 q))=some (Trans.Dict.BT.D 0 (rep1 (m+2)))
    rw [show ((Trans.Dict.BT.D 0 (rep1 (m+1)))==D1z)=false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [repl_rep1 f m (by omega)]
    rfl

theorem P_succ (m : Nat) :
    P (m+1) = P m ++ [((((m+2 : Nat) : Int), (1 : Int)))] := by
  unfold P
  rw [A_succ_last]
  simp [Nat.add_comm]

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1)) = L m := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [L, L, P_succ]
    unfold Trans.Recal.predP
    rw [show ((P m ++ [((((m+2 : Nat) : Int), (1 : Int)))]).length == 1) = false from by
      simp [P]]
    simp

theorem expand_M (n : Nat) :
    BMS.expand M n = [[0,0],[1,1]] ++
      (List.range n).map (fun a => [2+a,1]) := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n = some (M.take 1 ++
      ((List.range (n+1)).map (fun a =>
        ([[1+a*1*1,1+a*0*1]] : BMS.Matrix))).flatten) := rfl
  have hf : (fun a : Nat => ([[1+a*1*1,1+a*0*1]] : BMS.Matrix)) =
      fun a => [[1+a,1]] := by
    funext a
    simp
  have hflat (l : List Nat) :
      ((l.map (fun a => ([[1+a,1]] : BMS.Matrix))).flatten) =
        l.map (fun a => ([1+a,1] : BMS.Col)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.flatten_cons, ih]
      rfl
  rw [h, hf, hflat]
  rw [List.range_succ_eq_map]
  simp only [Option.getD_some, M, List.take, List.map_cons, List.map_map]
  change [([0,0] : BMS.Col), [1,1]] ++
      (List.range n).map ((fun a => ([1+a,1] : BMS.Col)) ∘ Nat.succ) = _
  congr 2
  funext a
  simp
  omega

theorem map_tail (m : Nat) :
    (((List.range m).map (fun a => ([2+a,1] : BMS.Col))) : BMS.Matrix).map
        (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int))) = A 2 m := by
  unfold A
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  apply Prod.ext <;> simp
  push_cast
  omega

theorem all_len_tail (m : Nat) :
    ((List.range m).map (fun a => ([2+a,1] : BMS.Col))).all
      (fun c => decide (c.length ≤ 2)) = true := by
  simp

/-- Link 1: expansion and parsing land on the reader ladder. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n) = some (L (n+1)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1]] : BMS.Matrix) ++
      (List.range n).map (fun a => ([2+a,1] : BMS.Col))).isEmpty = false from by
        cases n <;> rfl]
  rw [List.all_append, all_len_tail]
  simp only [List.all_cons, List.length_cons, List.length_nil,
    Bool.and_true, Bool.not_false, Bool.true_and, List.map_append,
    List.map_cons, List.map_nil]
  rw [map_tail]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n) == some (L (n+1))
#guard (List.range 8).all fun m => Trans.Recal.predP (L (m+1)) == L m
#guard rest12.any fun r => r.m == M && r.t == t

/-! Memo-table invariant for the requests made by the ascending ladder reader. -/

def Allowed : Nat → Option Int → Prop
  | 0, req => req=none ∨ req=some 0
  | k+1, req => req=none ∨ req=some (k:Int) ∨ req=some ((k+1:Nat):Int)

theorem Allowed_none (k : Nat) : Allowed k none := by
  cases k <;> simp [Allowed]

def Val (k : Nat) (req : Option Int) : Trans.Dict.BT :=
  if req=none then LBT k
  else if k=0 then .zero
  else if req=some ((k-1:Nat):Int) then
    if k=1 then LBT 1 else High
  else D1z

theorem Val_none (k : Nat) : Val k none=LBT k := by simp [Val]

theorem Val_top (k : Nat) : Val (k+1) (some ((k+1:Nat):Int))=D1z := by
  unfold Val
  rw [if_neg (by intro h; cases h),
    if_neg (by omega),
    if_neg (by
      intro h
      injection h with h
      omega)]

theorem Val_own_succ (k : Nat) :
    Val (k+2) (some ((k+1:Nat):Int))=High := by
  simp [Val]

theorem Val_one_own : Val 1 (some 0)=LBT 1 := rfl
theorem Val_one_top : Val 1 (some 1)=D1z := by
  change Val (0+1) (some ((0+1:Nat):Int))=D1z
  exact Val_top 0

theorem Allowed_zero_none : Allowed 0 none := Or.inl rfl
theorem Allowed_one_none : Allowed 1 none := Or.inl rfl
theorem Allowed_one_own : Allowed 1 (some 0) := Or.inr (Or.inl rfl)
theorem Allowed_one_top : Allowed 1 (some 1) := Or.inr (Or.inr rfl)

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  ∃ k req, p.1=(L k,req) ∧ Allowed k req ∧ p.2=Val k req

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p ∈ tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem L_inj (a b : Nat) (h : L a=L b) : a=b := by
  have hl := congrArg List.length h
  rw [length_L, length_L] at hl
  omega

theorem Sound_cons (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : Allowed k req) :
    Sound (((L k,req),Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h | h
  · subst h
    exact ⟨k,req,rfl,hr,rfl⟩
  · exact hs p h

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun q=>q.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h), ?_⟩
  have hb : p.1 == key := List.find?_some (p:=fun q=>q.1==key) (a:=p) h
  exact eq_of_beq hb

theorem value_of_good {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (hg : Good p) (k : Nat) (req : Option Int) (he : p.1=(L k,req)) :
    p.2=Val k req := by
  obtain ⟨j,r,hkey,_,hval⟩ := hg
  have hL : L j=L k := by simpa [hkey] using congrArg Prod.fst he
  have hj : j=k := L_inj j k hL
  subst hj
  have hr : r=req := by simpa [hkey] using congrArg Prod.snd he
  subst hr
  exact hval

theorem runAux_L0 (g : Nat) (req : Option Int) (hr : Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+1) (L 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+1) (L 0) req).run tbl).2 := by
  cases hf : tbl.find? (fun q=>q.1==(L 0,req)) with
  | some p =>
    rw [G1.run_hit g (L 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_of_good hg 0 req he,hs⟩
  | none =>
    have hj : Trans.Recal.lenI (L 0)-1=0 := by rw [lenI_L]; omega
    rw [Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, isReducedP_L 0, Bool.not_true,
      Bool.false_eq_true, if_false, hj,
      show ((0:Int)==0)=true from rfl, if_true,
      show Trans.Recal.gp0 (L 0) 0=0 from rfl,
      show Trans.Recal.gp1 (L 0) 0=0 from rfl,
      Bool.and_self]
    have hv : Val 0 req=.zero := by simp [Val,LBT]
    rw [hv]
    refine ⟨rfl,?_⟩
    simpa [hv] using Sound_cons tbl hs 0 req hr

theorem runAux_L1 (g : Nat) (req : Option Int) (hr : Allowed 1 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) (L 1) req).run tbl).1=Val 1 req ∧
      Sound ((Trans.Recal.runAux (g+2) (L 1) req).run tbl).2 := by
  cases hf : tbl.find? (fun q=>q.1==(L 1,req)) with
  | some p =>
    rw [G1.run_hit (g+1) (L 1) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_of_good hg 1 req he,hs⟩
  | none =>
    have hj : Trans.Recal.lenI (L 1)-1=1 := by rw [lenI_L]; omega
    rw [Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, isReducedP_L 1,
      show Trans.Recal.isPrincipalP (L 1)=true from isPrincipalP_P 0,
      Bool.not_true, Bool.false_eq_true, if_false, hj,
      show ((1:Int)==0)=false from rfl,
      show Trans.Recal.predP (L 1)=L 0 from predP_L 0]
    cases hrun : (Trans.Recal.runAux (g+1) (L 0) none) tbl with
    | mk a s =>
      have ih:=runAux_L0 g none Allowed_zero_none tbl hs
      rw [show (Trans.Recal.runAux (g+1) (L 0) none).run tbl=(a,s) from hrun] at ih
      have ha:a=.zero:=by
        rw [Val_none 0] at ih
        exact ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run, hrun,
        show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,if_true]
      rcases hr with h | h | h
      · subst h
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
          show Trans.Recal.gp1 (L 1) 1=1 from rfl]
        refine ⟨(Val_none 1).symm,?_⟩
        have ht:=Sound_cons s hsm 1 none Allowed_one_none
        rw [Val_none 1] at ht
        exact ht
      · subst h
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
          show Trans.Recal.gp1 (L 1) 1=1 from rfl]
        refine ⟨Val_one_own.symm,?_⟩
        have ht:=Sound_cons s hsm 1 (some 0) Allowed_one_own
        rw [Val_one_own] at ht
        exact ht
      · subst h
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
          show Trans.Recal.gp1 (L 1) 1=1 from rfl]
        refine ⟨Val_one_top.symm,?_⟩
        have ht:=Sound_cons s hsm 1 (some 1) Allowed_one_top
        rw [Val_one_top] at ht
        exact ht

set_option maxHeartbeats 1000000 in
theorem runAux_step (k g : Nat) (req : Option Int) (hr : Allowed (k+2) req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ (r : Option Int), Allowed (k+1) r →
      ∀ (s : Trans.Recal.Memo), Sound s →
        ((Trans.Recal.runAux ((k+1)+g+2) (L (k+1)) r).run s).1=Val (k+1) r ∧
          Sound ((Trans.Recal.runAux ((k+1)+g+2) (L (k+1)) r).run s).2) :
    ((Trans.Recal.runAux ((k+2)+g+2) (L (k+2)) req).run tbl).1=Val (k+2) req ∧
      Sound ((Trans.Recal.runAux ((k+2)+g+2) (L (k+2)) req).run tbl).2 := by
  cases hf : tbl.find? (fun q=>q.1==(L (k+2),req)) with
  | some p =>
    rw [show (k+2)+g+2=((k+1)+g+2)+1 by omega,
      G1.run_hit ((k+1)+g+2) (L (k+2)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_of_good hg (k+2) req he,hs⟩
  | none =>
    have hj : Trans.Recal.lenI (L (k+2))-1=(k:Int)+2 := by
      rw [lenI_L]
      push_cast
      omega
    rw [show (k+2)+g+2=((k+1)+g+2)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, isReducedP_L (k+2),
      show Trans.Recal.isPrincipalP (L (k+2))=true from by
        simpa [L] using isPrincipalP_P (k+1),
      Bool.not_true, Bool.false_eq_true, if_false, hj,
      show (((k:Int)+2)==0)=false from by
        exact beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (k+2))=L (k+1) from predP_L (k+1)]
    cases hrun : (Trans.Recal.runAux ((k+1)+g+2) (L (k+1)) none) tbl with
    | mk a s =>
      have ih1:=ih none (by simp [Allowed]) tbl hs
      rw [show (Trans.Recal.runAux ((k+1)+g+2) (L (k+1)) none).run tbl=(a,s)
        from hrun] at ih1
      have ha:a=LBT (k+1):=by simpa [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run, hrun,
        show ((LBT (k+1))==Trans.Dict.BT.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (L (k+2)) 0 ((k:Int)+2) 0=(k:Int)+1 from by
          simpa only [L, show (((k+1:Nat):Int)+1)=(k:Int)+2 by omega,
            show (((k+1:Nat):Int))=(k:Int)+1 by omega] using fpar_P_top (k+1),
        show Trans.Recal.adm (L (k+2)) ((k:Int)+1)=(k:Int)+1 from by
          simpa only [L, show (((k+1:Nat):Int))=(k:Int)+1 by omega] using
            adm_P_topParent (k+1)]
      cases hrun2 : (Trans.Recal.runAux ((k+1)+g+2) (L (k+1))
          (some ((k:Int)+1))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((k:Int)+1)) (by simp [Allowed]) s hsm
        rw [show (Trans.Recal.runAux ((k+1)+g+2) (L (k+1))
          (some ((k:Int)+1))).run s=(c1,s2) from hrun2] at ih2
        have hvtop : Val (k+1) (some ((k:Int)+1))=D1z := by
          rw [← show (((k+1:Nat):Int))=(k:Int)+1 by omega]
          exact Val_top k
        have hc1:c1=D1z:=ih2.1.trans hvtop
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run, hrun2,
          show Trans.Recal.transTypeMain (L (k+2)) ((k:Int)+1) ((k:Int)+2)=3 from by
            simpa only [L] using transType_P_succ k,
          show Trans.Recal.mkC2 (L (k+2)) ((k:Int)+1) ((k:Int)+2) 3 D1z=High from by
            simpa only [L] using mkC2_P_succ k]
        rcases hr with h | h | h
        · subst h
          rw [repl_LBT ((LBT (k+1)).size+(D1z.size+High.size+4)) k (by
            rw [size_LBT_succ]
            omega)]
          simp only [Option.getD_some]
          exact ⟨Val_none (k+2),Sound_cons s2 hsm2 (k+2) none (by simp [Allowed])⟩
        · subst h
          simp only [show (((k+1:Nat):Int)<(k:Int)+2) from by omega,if_true,
            StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
            MonadStateOf.get, Id.run]
          cases hrun3 : (Trans.Recal.runAux ((k+1)+g+2) (L (k+1))
              (some ((k+1:Nat):Int))) s2 with
          | mk c0 s3 =>
            have ih3:=ih (some ((k+1:Nat):Int)) (by simp [Allowed]) s2 hsm2
            rw [show (Trans.Recal.runAux ((k+1)+g+2) (L (k+1))
              (some ((k+1:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
            have hc0:c0=D1z:=ih3.1.trans (Val_top k)
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (G1.isMarkedB_self D1z),
              G1.replMark_self (D1z.size+(D1z.size+High.size+4)) 1 .zero High (by omega)]
            simp only [Option.getD_some]
            refine ⟨(Val_own_succ k).symm,?_⟩
            have ht:=Sound_cons s3 hsm3 (k+2)
              (some ((k+1:Nat):Int)) (by simp [Allowed])
            rw [Val_own_succ k] at ht
            exact ht
        · subst h
          simp only [show ¬(((k+2:Nat):Int)<(k:Int)+2) by omega,if_false,
            show Trans.Recal.gp1 (L (k+2)) ((k:Int)+2)=1 from by
              simpa only [L] using gp1_P_pos (k+1) ((k:Int)+2) (by omega) (by omega),
            StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
            MonadStateOf.get, Id.run]
          refine ⟨?_,?_⟩
          · exact (Val_top (k+1)).symm
          · have ht:=Sound_cons s2 hsm2 (k+2) (some (((k+1)+1:Nat):Int))
              (by simp [Allowed])
            rw [Val_top (k+1)] at ht
            exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_L (k g : Nat) (req : Option Int) (hr : Allowed k req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+2) (L k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+2) (L k) req).run tbl).2 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ g req, Allowed k req →
    ∀ tbl, Sound tbl →
      ((Trans.Recal.runAux (k+g+2) (L k) req).run tbl).1=Val k req ∧
        Sound ((Trans.Recal.runAux (k+g+2) (L k) req).run tbl).2) k ?_
      g req hr tbl hs
  intro k ih g req hr tbl hs
  cases k with
    | zero =>
      simpa only [Nat.zero_add, Nat.add_assoc] using
        runAux_L0 (g+1) req hr tbl hs
    | succ k =>
      cases k with
      | zero =>
        simpa only [Nat.zero_add, Nat.add_assoc] using
          runAux_L1 (g+1) req hr tbl hs
      | succ k =>
        apply runAux_step k g req hr tbl hs
        intro r hallowed s hsound
        exact ih (k+1) (by omega) g r hallowed s hsound

/-- Link 2: the recalibrated reader follows the whole ascending ladder. -/
theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m)=LBT m := by
  have hb : m+2≤Trans.Recal.transFuel (L m) := by
    show m+2≤40+6*((L m).length+Trans.Recal.maxE (L m))
    rw [length_L]
    omega
  have h : Trans.Recal.transFuel (L m)=
      m+(Trans.Recal.transFuel (L m)-m-2)+2 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L m)) (L m) none).run []).1=_
  rw [h]
  simpa only [Val_none] using
    (runAux_L m _ none (Allowed_none m) [] Sound_nil).1

#guard (List.range 8).all fun m => Trans.Recal.transPort (L m)==LBT m

/-! Link 3 and the composed row theorem. -/

theorem rep1_eq_G4Dict : ∀ n, rep1 n=G4Dict.rep1 n
  | 0 => rfl
  | n+1 => by rw [rep1,G4Dict.rep1,rep1_eq_G4Dict n]

theorem dict_LBT (n : Nat) : Trans.Dict.dict (LBT (n+1))=fC n := by
  rw [LBT,PBT,rep1_eq_G4Dict]
  exact G4Dict.dict_D0_rep1_fC n

theorem one_plus_fC (n : Nat) : plus TM.Term.one (fC n)=fC n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => rfl

/-- The selected `ψ₀(Ω₂)` row agrees with its closed expansion sequence for every `n`. -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fC n) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map Trans.Recal.transPort).map
          (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=_
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    cases n <;> rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_L,dict_LBT,one_plus_fC]

#guard (List.range 8).all fun n => Trans.oR (BMS.expand M n)==some (fC n)
#print axioms oR_M

end G4
end Rows.Selected
