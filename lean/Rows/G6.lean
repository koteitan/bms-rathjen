import Rows.G6Dict

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G6

def M : BMS.Matrix := [[0,0],[1,1],[2,2],[2,2]]
def t : Term := psi (Z zero) (add (Z (phi zero zero)) (Z (phi zero zero)))

/-- The alternating row-one/row-two tail, refined to one reader step per column. -/
def T (m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k =>
    (((((k+5)/2 : Nat) : Int)), ((((k%2)+1 : Nat) : Int)))

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS :=
  (0,0) :: (1,1) :: (2,2) :: T m

abbrev X : Trans.Dict.BT := .D 2 .zero

/-- Repeated Buchholz wrapper created by a tail pair. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0, b => b
  | k+1, b => .sum X (.D 1 (W k b))

/-- Reader output on every one-column prefix of the alternating ladder. -/
def LBT : Nat → Trans.Dict.BT
  | 0 => .D 0 X
  | m+1 => if m%2=0 then .D 0 (W (m/2+2) .zero)
      else .D 0 (W ((m+1)/2+1) X)

theorem T_succ (m : Nat) :
    T (m+1)=T m ++
      [((((m+5)/2:Nat):Int),((((m%2)+1:Nat):Int)))] := by
  unfold T
  rw [List.range_succ,List.map_append]
  rfl

theorem L_succ (m : Nat) :
    L (m+1)=L m ++
      [((((m+5)/2:Nat):Int),((((m%2)+1:Nat):Int)))] := by
  unfold L
  rw [T_succ]
  simp only [List.cons_append,List.append_assoc]

theorem length_T (m : Nat) : (T m).length=m := by simp [T]

theorem length_L (m : Nat) : (L m).length=m+3 := by
  simp [L,length_T]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+3 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1))=L m := by
  rw [L_succ]
  unfold Trans.Recal.predP
  rw [show ((L m ++ [((((m+5)/2:Nat):Int),((((m%2)+1:Nat):Int)))]).length==1)=false from by
    rw [List.length_append,length_L]
    simp]
  simp

/-! ### Link 1: expansion and parsing. -/

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,2]] ++
      ((List.range n).map fun a =>
        ([[2+a,1],[3+a,2]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 1 ++
      ((List.range (n+1)).map fun a =>
        ([[1+a*1*1,1+a*0*1],[2+a*1*1,2+a*0*1]] : BMS.Matrix)).flatten) := rfl
  have hf : (fun a : Nat =>
      ([[1+a*1*1,1+a*0*1],[2+a*1*1,2+a*0*1]] : BMS.Matrix))=
      fun a => [[1+a,1],[2+a,2]] := by
    funext a
    simp
  rw [h,hf,List.range_succ_eq_map]
  simp only [Option.getD_some,M,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.singleton_append]
  change [([0,0]:BMS.Col),[1,1],[2,2]] ++
      ((List.range n).map ((fun a => ([[1+a,1],[2+a,2]]:BMS.Matrix)) ∘ Nat.succ)).flatten = _
  have hblocks :
      ((fun a : Nat => ([[1+a,1],[2+a,2]]:BMS.Matrix)) ∘ Nat.succ)=
        fun a => [[2+a,1],[3+a,2]] := by
    funext a
    simp
    constructor <;> omega
  rw [hblocks]

theorem T_two_mul (n : Nat) :
    T (2*n)=((List.range n).map fun a =>
      ([(((a+2:Nat):Int),(1:Int)),(((a+3:Nat):Int),(2:Int))] : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,T_succ,T_succ,ih,List.range_succ,
      List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc]
    simp only [List.singleton_append]
    congr 1
    congr 1
    · apply Prod.ext <;> simp <;> omega
    · congr 1
      apply Prod.ext <;> simp <;> omega

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[2+a,1],[3+a,2]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=T (2*n) := by
  rw [T_two_mul]
  rw [List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp
  constructor <;> push_cast <;> omega

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[2+a,1],[3+a,2]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by
  simp

/-- Link 1: the expanded row lands on the even prefixes of the refined ladder. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (2*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,2]]:BMS.Matrix) ++
      ((List.range n).map fun a =>
        ([[2+a,1],[3+a,2]] : BMS.Matrix)).flatten).isEmpty=false from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (2*n))
#guard (List.range 12).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard rest12.any fun r => r.m==M && r.t==t

/-! ### Structural facts for the alternating tail. -/

theorem getD_T (m k : Nat) (hk : k<m) :
    (T m).getD k (0,0)=
      (((((k+5)/2:Nat):Int),((((k%2)+1:Nat):Int)))) := by
  unfold T
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem gp0_T (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (T m) (k:Int)=((((k+5)/2:Nat):Int)) := by
  show (if (k:Int)<0 then 0 else ((T m).getD k (0,0)).1)=_
  rw [if_neg (by omega),getD_T m k hk]

theorem gp1_T (m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (T m) (k:Int)=((((k%2)+1:Nat):Int)) := by
  show (if (k:Int)<0 then 0 else ((T m).getD k (0,0)).2)=_
  rw [if_neg (by omega),getD_T m k hk]

theorem lenI_T (m : Nat) : Trans.Recal.lenI (T m)=(m:Int) := by
  unfold Trans.Recal.lenI
  rw [length_T]

theorem fpar_T_odd (m n : Nat) (h : 2*n+1<m) :
    Trans.Recal.fpar (T m) 0 (2*n+1:Nat) 0=(2*n:Nat) := by
  have h0:2*n<m:=by omega
  have gt:Trans.Recal.gp0 (T m) (2*n+1:Nat)=(n+3:Nat) := by
    simpa only [show (2*n+1+5)/2=n+3 by omega] using gp0_T m (2*n+1) h
  have gc:Trans.Recal.gp0 (T m) (2*n:Nat)=(n+2:Nat) := by
    simpa only [show (2*n+5)/2=n+2 by omega] using gp0_T m (2*n) h0
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  simp only [Trans.Recal.fpar0Aux]
  rw [show ((2*n+1:Nat):Int)-1=(2*n:Nat) by omega,gt,gc,
    if_neg (by omega),if_pos (by omega)]

theorem fpar_T_even (m n : Nat) (h : 2*n+2<m) :
    Trans.Recal.fpar (T m) 0 (2*n+2:Nat) 0=(2*n:Nat) := by
  have h0:2*n<m:=by omega
  have h1:2*n+1<m:=by omega
  have gt:Trans.Recal.gp0 (T m) (2*n+2:Nat)=(n+3:Nat) := by
    simpa only [show (2*n+2+5)/2=n+3 by omega] using gp0_T m (2*n+2) h
  have gc1:Trans.Recal.gp0 (T m) (2*n+1:Nat)=(n+3:Nat) := by
    simpa only [show (2*n+1+5)/2=n+3 by omega] using gp0_T m (2*n+1) h1
  have gc0:Trans.Recal.gp0 (T m) (2*n:Nat)=(n+2:Nat) := by
    simpa only [show (2*n+5)/2=n+2 by omega] using gp0_T m (2*n) h0
  obtain ⟨p,hmp⟩ : ∃ p,m=p+1 := ⟨m-1,by omega⟩
  subst m
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  simp only [Trans.Recal.fpar0Aux]
  rw [show ((2*n+2:Nat):Int)-1=(2*n+1:Nat) by omega,gt,gc1,
    if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [Trans.Recal.fpar0Aux.eq_def,if_neg (by omega)]
  rw [show ((2*n+1:Nat):Int)-1=(2*n:Nat) by omega,gc0,if_pos (by omega)]

def parentT (k : Nat) : Nat := if k%2=1 then k-1 else k-2

theorem fpar_T_pos (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (T m) 0 (k:Int) 0=(parentT k:Nat) := by
  unfold parentT
  split
  · rename_i hodd
    have heq:k=2*(k/2)+1:=by omega
    rw [heq] at hk ⊢
    simpa using fpar_T_odd m (k/2) hk
  · rename_i hnodd
    have heven:k%2=0:=by omega
    have heq:k=2*((k-2)/2)+2:=by omega
    rw [heq] at hk ⊢
    simpa using fpar_T_even m ((k-2)/2) hk

theorem parentT_lt (k : Nat) (hk : 0<k) : parentT k<k := by
  unfold parentT
  split <;> omega

theorem isAncAux_T (k : Nat) : ∀ m f : Nat, k<m → k<f →
    Trans.Recal.isAncAux f (T m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, k<m → k<f →
    Trans.Recal.isAncAux f (T m) 0 (k:Int) 0=true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · have hkpos:0<k:=by omega
      rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_T_pos m k hkpos hkm]
      rw [show (((parentT k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk m f
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf))

theorem isAnc_T (m k : Nat) (hk : k<m) :
    Trans.Recal.isAnc (T m) 0 (k:Int) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_T]; omega),length_T]
  exact isAncAux_T k m (m+1) hk (by omega)

theorem fAncAux_T_last (k : Nat) : ∀ m f : Nat, ∀ acc : List Int,
    k<m → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (T m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, ∀ acc:List Int,
    k<m → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (T m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih m f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      have hp:Trans.Recal.fpar (T m) 0 0 0=-1:=by
        unfold Trans.Recal.fpar
        rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl)]
        simp only [Trans.Recal.fpar0Aux]
        rw [if_pos (by omega)]
      rw [show ((0:Nat):Int)=0 from rfl,hp,if_neg (by omega)]
      exact hlast
    · have hkpos:0<k:=by omega
      rw [fpar_T_pos m k hkpos hkm,if_pos (by omega)]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk m f (acc++[((parentT k:Nat):Int)])
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf)) (by simp)

theorem fAnc_T_last (m : Nat) (hm : 0<m) :
    (Trans.Recal.fAnc (T m) 0 ((m-1:Nat):Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_T]; omega),length_T]
  exact fAncAux_T_last (m-1) m (m+1) [((m-1:Nat):Int)]
    (by omega) (by omega) (by simp)

theorem slice_T_full (m : Nat) :
    Trans.Recal.slice (T m) 0 (m:Int)=T m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show ((m:Int)-0).toNat=m from by omega]
  simpa only [length_T] using (List.take_length (l:=T m))

theorem ppair_T : ∀ m : Nat,
    Trans.Recal.ppair (T m)=if m=0 then [] else [T m]
  | 0 => rfl
  | m+1 => by
    unfold Trans.Recal.ppair
    rw [length_T]
    simp only [show ¬m+1=0 by omega,if_false,Trans.Recal.ppairAux]
    rw [show Trans.Recal.lenI (T (m+1))-1=(m:Int) by rw [lenI_T]; omega,
      if_neg (by omega)]
    have hf:(Trans.Recal.fAnc (T (m+1)) 0 (m:Int) 0).getLast?=some 0 := by
      simpa only [Nat.add_sub_cancel] using fAnc_T_last (m+1) (by omega)
    rw [hf]
    simp only [Option.getD_some]
    rw [show (0:Int)-1=-1 by omega,if_pos (by omega),
      show (m:Int)+1=((m+1:Nat):Int) by omega,slice_T_full]

/-! ### Structure of the complete ladder. -/

theorem fpar_L_one (m : Nat) : Trans.Recal.fpar (L m) 0 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),
    show Trans.Recal.gp0 (L m) 1=1 from rfl,length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (1:Int)-1=0 by omega,
    if_neg (by omega),show Trans.Recal.gp0 (L m) 0=0 from rfl,if_pos (by omega)]

theorem fpar_L_two (m : Nat) : Trans.Recal.fpar (L m) 0 2 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),
    show Trans.Recal.gp0 (L m) 2=2 from rfl,length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (2:Int)-1=1 by omega,
    if_neg (by omega),show Trans.Recal.gp0 (L m) 1=1 from rfl,if_pos (by omega)]

theorem fpar_L_three (m : Nat) :
    Trans.Recal.fpar (L (m+1)) 0 3 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L (m+1)) 3=2 from by
    simp [Trans.Recal.gp0,L,T],if_neg (by omega)]
  rw [show (3:Int)-1=2 by omega,
    show Trans.Recal.gp0 (L (m+1)) 2=2 from rfl,if_neg (by omega),
    if_neg (by omega)]
  rw [show (2:Int)-1=1 by omega,
    show Trans.Recal.gp0 (L (m+1)) 1=1 from rfl,if_pos (by omega)]

theorem getD_L_tail (m k : Nat) (hk : k<m) :
    (L m).getD (k+3) (0,0)=
      (((((k+5)/2:Nat):Int),((((k%2)+1:Nat):Int)))) := by
  show (T m).getD k (0,0)=_
  exact getD_T m k hk

theorem gp0_L_tail (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (L m) ((k+3:Nat):Int)=((((k+5)/2:Nat):Int)) := by
  show (if ((k+3:Nat):Int)<0 then 0 else
    ((L m).getD (k+3) (0,0)).1)=_
  rw [if_neg (by omega),getD_L_tail m k hk]

theorem fpar_L_tail_odd (m n : Nat) (h : 2*n+1<m) :
    Trans.Recal.fpar (L m) 0 ((2*n+1+3:Nat):Int) 0=((2*n+3:Nat):Int) := by
  have h0:2*n<m:=by omega
  have gt:Trans.Recal.gp0 (L m) ((2*n+1+3:Nat):Int)=(n+3:Nat) := by
    simpa only [show (2*n+1+5)/2=n+3 by omega] using gp0_L_tail m (2*n+1) h
  have gc:Trans.Recal.gp0 (L m) ((2*n+3:Nat):Int)=(n+2:Nat) := by
    simpa only [show (2*n+5)/2=n+2 by omega] using gp0_L_tail m (2*n) h0
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [show ((2*n+1+3:Nat):Int)-1=(2*n+3:Nat) by omega,gt,gc,
    if_neg (by omega),if_pos (by omega)]

theorem fpar_L_tail_even (m n : Nat) (h : 2*n+2<m) :
    Trans.Recal.fpar (L m) 0 ((2*n+2+3:Nat):Int) 0=((2*n+3:Nat):Int) := by
  have h0:2*n<m:=by omega
  have h1:2*n+1<m:=by omega
  have gt:Trans.Recal.gp0 (L m) ((2*n+2+3:Nat):Int)=(n+3:Nat) := by
    simpa only [show (2*n+2+5)/2=n+3 by omega] using gp0_L_tail m (2*n+2) h
  have gc1:Trans.Recal.gp0 (L m) ((2*n+1+3:Nat):Int)=(n+3:Nat) := by
    simpa only [show (2*n+1+5)/2=n+3 by omega] using gp0_L_tail m (2*n+1) h1
  have gc0:Trans.Recal.gp0 (L m) ((2*n+3:Nat):Int)=(n+2:Nat) := by
    simpa only [show (2*n+5)/2=n+2 by omega] using gp0_L_tail m (2*n) h0
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [show ((2*n+2+3:Nat):Int)-1=(2*n+1+3:Nat) by omega,gt,gc1,
    if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [show ((2*n+1+3:Nat):Int)-1=(2*n+3:Nat) by omega,gc0,
    if_neg (by omega),if_pos (by omega)]

theorem fpar_L_tail_pos (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (L m) 0 ((k+3:Nat):Int) 0=((parentT k+3:Nat):Int) := by
  unfold parentT
  split
  · rename_i hodd
    have heq:k=2*(k/2)+1:=by omega
    rw [heq] at hk ⊢
    simpa using fpar_L_tail_odd m (k/2) hk
  · rename_i hnodd
    have heven:k%2=0:=by omega
    have heq:k=2*((k-2)/2)+2:=by omega
    rw [heq] at hk ⊢
    simpa using fpar_L_tail_even m ((k-2)/2) hk

def parentL : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | k+4 => parentT (k+1)+3

theorem parentL_lt (k : Nat) (hk : 0<k) : parentL k<k := by
  match k with
  | 0 => simp [parentL] at hk
  | 1 => simp [parentL]
  | 2 => simp [parentL]
  | 3 => simp [parentL]
  | q+4 =>
    simp only [parentL]
    have h:=parentT_lt (q+1) (by omega)
    omega

theorem fpar_L_pos (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar (L m) 0 (k:Int) 0=(parentL k:Nat) := by
  match k with
  | 0 => omega
  | 1 => exact fpar_L_one m
  | 2 => exact fpar_L_two m
  | 3 =>
    have hm:0<m:=by omega
    simpa only [parentL,show m-1+1=m by omega] using fpar_L_three (m-1)
  | q+4 =>
    have hq:q+1<m:=by omega
    simpa [parentL] using fpar_L_tail_pos m (q+1) (by omega) hq

theorem isAncAux_L (k : Nat) : ∀ m f : Nat, k<m+3 → k<f →
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, k<m+3 → k<f →
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · have hkpos:0<k:=by omega
      rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_L_pos m k hkpos hkm]
      rw [show (((parentL k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hpk:=parentL_lt k hkpos
      exact ih (parentL k) hpk m f
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf))

theorem isAnc_L (m k : Nat) (hk : k<m+3) :
    Trans.Recal.isAnc (L m) 0 (k:Int) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  exact isAncAux_L k m (m+4) hk (by omega)

theorem isPrincipalP_L (m : Nat) : Trans.Recal.isPrincipalP (L m)=true := by
  have ha:=isAnc_L m (m+2) (by omega)
  have ha':Trans.Recal.isAnc (L m) 0 (Trans.Recal.lenI (L m)-1) 0=true := by
    rw [lenI_L]
    simpa only [show (m:Int)+3-1=((m+2:Nat):Int) by omega] using ha
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (L m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_L]
    simp,ha']
  rfl

theorem fpar0_L_one (m : Nat) : Trans.Recal.fpar0 (L m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega)]
  change (if Trans.Recal.gp0 (L m) 0<1 then 0 else _)=0
  rw [show Trans.Recal.gp0 (L m) 0=0 from rfl,if_pos (by omega)]

theorem fpar0_L_two (m : Nat) : Trans.Recal.fpar0 (L m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega)]
  change (if Trans.Recal.gp0 (L m) 1<2 then 1 else _)=1
  rw [show Trans.Recal.gp0 (L m) 1=1 from rfl,if_pos (by omega)]

theorem fpar0_L_three_lb (m : Nat) :
    Trans.Recal.fpar0 (L (m+1)) 3 2=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega)]
  rw [show (3:Int)-1=2 by omega,
    show Trans.Recal.gp0 (L (m+1)) 3=2 from by simp [Trans.Recal.gp0,L,T]]
  change (if Trans.Recal.gp0 (L (m+1)) 2<2 then 2
    else Trans.Recal.fpar0Aux (m+4) (L (m+1)) 2 1 2)=-1
  rw [show Trans.Recal.gp0 (L (m+1)) 2=2 from rfl,if_neg (by omega)]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux,if_pos (by omega)]

theorem fpar0_L_three_zero (m : Nat) :
    Trans.Recal.fpar0 (L (m+1)) 3 0=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega)]
  rw [show (3:Int)-1=2 by omega,
    show Trans.Recal.gp0 (L (m+1)) 3=2 from by simp [Trans.Recal.gp0,L,T]]
  change (if Trans.Recal.gp0 (L (m+1)) 2<2 then 2
    else Trans.Recal.fpar0Aux (m+4) (L (m+1)) 2 1 0)=1
  rw [show Trans.Recal.gp0 (L (m+1)) 2=2 from rfl,if_neg (by omega)]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega)]
  change (if Trans.Recal.gp0 (L (m+1)) 1<2 then 1 else _)=1
  rw [show Trans.Recal.gp0 (L (m+1)) 1=1 from rfl,if_pos (by omega)]

theorem gp1_L_three (m : Nat) :
    Trans.Recal.gp1 (L (m+1)) 3=1 := by
  show (if (3:Int)<0 then 0 else ((L (m+1)).getD 3 (0,0)).2)=1
  rw [if_neg (by omega),getD_L_tail (m+1) 0 (by omega)]
  rfl

theorem fpar1_L_one (m : Nat) : Trans.Recal.fpar (L m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [show Trans.Recal.gp1 (L m) 1=1 from rfl,length_L]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_one,if_neg (by omega),
    show Trans.Recal.gp1 (L m) 0=0 from rfl,if_pos (by omega)]

theorem fpar1_L_two (m : Nat) : Trans.Recal.fpar (L m) 1 2 1=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [show Trans.Recal.gp1 (L m) 2=2 from rfl,length_L]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_two,if_neg (by omega),
    show Trans.Recal.gp1 (L m) 1=1 from rfl,if_pos (by omega)]

theorem fpar1_L_three_lb (m : Nat) :
    Trans.Recal.fpar (L (m+1)) 1 3 2=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_three,length_L]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_three_lb,if_pos (by omega)]

theorem fpar1_L_three_zero (m : Nat) :
    Trans.Recal.fpar (L (m+1)) 1 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_three,length_L]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_three_zero,if_neg (by omega),
    show Trans.Recal.gp1 (L (m+1)) 1=1 from rfl,if_neg (by omega)]
  rw [fpar0_L_one,if_neg (by omega),
    show Trans.Recal.gp1 (L (m+1)) 0=0 from rfl,if_pos (by omega)]

theorem isParentP_L_one (m : Nat) :
    Trans.Recal.isParentP (L m) 1 1 0=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_L_one,lenI_L]
  rw [show decide ((0:Int)<(m:Int)+3)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_L_two (m : Nat) :
    Trans.Recal.isParentP (L m) 1 2 1=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_L_two,lenI_L]
  rw [show decide ((1:Int)<(m:Int)+3)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_L_three (m : Nat) :
    Trans.Recal.isParentP (L (m+1)) 1 3 2=false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_L_three_lb]
  simp

theorem trMax_L_zero : Trans.Recal.trMax (L 0)=2 := by decide

theorem trMax_L_succ (m : Nat) : Trans.Recal.trMax (L (m+1))=2 := by
  show Trans.Recal.trMaxAux ((L (m+1)).length+1) (L (m+1)) 0=2
  rw [length_L]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_L]; omega)]
  change (if !Trans.Recal.isParentP (L (m+1)) 1 1 0 then 0
    else Trans.Recal.trMaxAux (m+4) (L (m+1)) 1)=2
  rw [isParentP_L_one]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_L]; omega)]
  change (if !Trans.Recal.isParentP (L (m+1)) 1 2 1 then 1
    else Trans.Recal.trMaxAux (m+3) (L (m+1)) 2)=2
  rw [isParentP_L_two]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_L]; omega)]
  change (if !Trans.Recal.isParentP (L (m+1)) 1 3 2 then 2
    else Trans.Recal.trMaxAux (m+2) (L (m+1)) 3)=2
  rw [isParentP_L_three]
  rfl

theorem trMax_L : ∀ m : Nat, Trans.Recal.trMax (L m)=2
  | 0 => trMax_L_zero
  | m+1 => trMax_L_succ m

theorem brF_L_zero : Trans.Recal.brF (L 0)=[] := by rfl

theorem brF_L_succ (m : Nat) :
    Trans.Recal.brF (L (m+1))=[T (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_L]
  change Trans.Recal.ppair (T (m+1))=[T (m+1)]
  rw [ppair_T]
  simp

theorem firstNodes_L_zero : Trans.Recal.firstNodes (L 0)=[3] := by rfl

theorem firstNodes_L_succ (m : Nat) :
    Trans.Recal.firstNodes (L (m+1))=[3,((m+4:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L_succ,trMax_L]
  simp [length_T]
  omega

theorem joints_L_zero : Trans.Recal.joints (L 0)=[] := by rfl

theorem joints_L_succ (m : Nat) :
    Trans.Recal.joints (L (m+1))=[1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_L_succ]
  change [Trans.Recal.fpar (L (m+1)) 0 3 0]=[1]
  rw [fpar_L_three]

/-! ### Reduction on the shifted alternating family. -/

/-- A tail beginning with a row-two/row-one pair at first coordinate `a`. -/
def A (a m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k =>
    ((((a+k/2:Nat):Int)),(((2-k%2:Nat):Int)))

/-- A positive row-one head followed by an alternating tail. -/
def K (d a m : Nat) : Trans.Recal.PS := (((d:Nat):Int),(1:Int))::A a m

/-- The same family below a zero root. -/
def C (d a m : Nat) : Trans.Recal.PS := (0,0)::K d a m

theorem length_A (a m : Nat) : (A a m).length=m := by simp [A]

theorem length_K (d a m : Nat) : (K d a m).length=m+1 := by
  simp [K,length_A]

theorem length_C (d a m : Nat) : (C d a m).length=m+2 := by
  simp [C,length_K]

theorem lenI_C (d a m : Nat) : Trans.Recal.lenI (C d a m)=(m:Int)+2 := by
  unfold Trans.Recal.lenI
  rw [length_C]
  omega

theorem getD_A (a m k : Nat) (hk : k<m) :
    (A a m).getD k (0,0)=
      ((((a+k/2:Nat):Int)),(((2-k%2:Nat):Int))) := by
  unfold A
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem gp0_C_tail (d a m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (C d a m) ((k+2:Nat):Int)=((a+k/2:Nat):Int) := by
  show (if ((k+2:Nat):Int)<0 then 0 else
    ((C d a m).getD (k+2) (0,0)).1)=_
  rw [if_neg (by omega)]
  show ((A a m).getD k (0,0)).1=_
  rw [getD_A a m k hk]

theorem gp1_C_tail (d a m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (C d a m) ((k+2:Nat):Int)=((2-k%2:Nat):Int) := by
  show (if ((k+2:Nat):Int)<0 then 0 else
    ((C d a m).getD (k+2) (0,0)).2)=_
  rw [if_neg (by omega)]
  show ((A a m).getD k (0,0)).2=_
  rw [getD_A a m k hk]

theorem fpar_C_one (d a m : Nat) (hd : 0<d) :
    Trans.Recal.fpar (C d a m) 0 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega),if_pos (by rfl),length_C]
  simp only [Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (C d a m) 1=(d:Int) from rfl,
    show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (C d a m) 0=0 from rfl,if_pos (by omega)]

theorem fpar_C_two (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 0<m) :
    Trans.Recal.fpar (C d a m) 0 2 0=1 := by
  have hgt : Trans.Recal.gp0 (C d a m) 2=(a:Int) := by
    simpa using gp0_C_tail d a m 0 hm
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega),if_pos (by rfl),length_C]
  rw [show (2:Int)-1=1 by omega]
  change Trans.Recal.fpar0Aux (m+2+1) (C d a m)
    (Trans.Recal.gp0 (C d a m) 2) 1 0=1
  rw [hgt]
  change (if (1:Int)<0 then -1 else
    if Trans.Recal.gp0 (C d a m) 1<(a:Int) then 1 else _)=1
  rw [if_neg (by omega),
    show Trans.Recal.gp0 (C d a m) 1=(d:Int) from rfl,
    if_pos (by push_cast; omega)]

theorem fpar_C_three (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 1<m) :
    Trans.Recal.fpar (C d a m) 0 3 0=1 := by
  have hgt : Trans.Recal.gp0 (C d a m) 3=(a:Int) := by
    simpa using gp0_C_tail d a m 1 (by omega)
  have hgp2 : Trans.Recal.gp0 (C d a m) 2=(a:Int) := by
    simpa using gp0_C_tail d a m 0 (by omega)
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega),if_pos (by rfl),length_C]
  rw [show (3:Int)-1=2 by omega]
  change Trans.Recal.fpar0Aux (m+2+1) (C d a m)
    (Trans.Recal.gp0 (C d a m) 3) 2 0=1
  rw [hgt]
  change (if (2:Int)<0 then -1 else
    if Trans.Recal.gp0 (C d a m) 2<(a:Int) then 2 else
      Trans.Recal.fpar0Aux (m+2) (C d a m) (a:Int) 1 0)=1
  rw [if_neg (by omega),hgp2,if_neg (by omega)]
  change (if (1:Int)<0 then -1 else
    if Trans.Recal.gp0 (C d a m) 1<(a:Int) then 1 else _)=1
  rw [if_neg (by omega),
    show Trans.Recal.gp0 (C d a m) 1=(d:Int) from rfl,
    if_pos (by push_cast; omega)]

theorem fpar_C_tail_even (d a m n : Nat) (hd : 0<d) (hda : d<a)
    (h : 2*n+2<m) :
    Trans.Recal.fpar (C d a m) 0 ((2*n+2+2:Nat):Int) 0=
      ((2*n+1+2:Nat):Int) := by
  have h1:2*n+1<m:=by omega
  have gt:=gp0_C_tail d a m (2*n+2) h
  have gc:=gp0_C_tail d a m (2*n+1) h1
  have gt' : Trans.Recal.gp0 (C d a m) ((2*n+2+2:Nat):Int)=(a+n+1:Nat) := by
    simpa only [show (a+(2*n+2)/2:Nat)=a+n+1 by omega] using gt
  have gc' : Trans.Recal.gp0 (C d a m) ((2*n+1+2:Nat):Int)=(a+n:Nat) := by
    simpa only [show (a+(2*n+1)/2:Nat)=a+n by omega] using gc
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega),if_pos (by rfl),length_C]
  rw [show ((2*n+2+2:Nat):Int)-1=((2*n+1+2:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2+1) (C d a m)
    (Trans.Recal.gp0 (C d a m) ((2*n+2+2:Nat):Int))
    ((2*n+1+2:Nat):Int) 0=((2*n+1+2:Nat):Int)
  rw [gt']
  change (if ((2*n+1+2:Nat):Int)<0 then -1 else
    if Trans.Recal.gp0 (C d a m) ((2*n+1+2:Nat):Int)<(a+n+1:Nat)
      then ((2*n+1+2:Nat):Int) else _)=_
  rw [if_neg (by omega),gc',if_pos (by omega)]

theorem fpar_C_tail_odd (d a m n : Nat) (hd : 0<d) (hda : d<a)
    (h : 2*n+3<m) :
    Trans.Recal.fpar (C d a m) 0 ((2*n+3+2:Nat):Int) 0=
      ((2*n+1+2:Nat):Int) := by
  have h1:2*n+2<m:=by omega
  have h0:2*n+1<m:=by omega
  have gt:=gp0_C_tail d a m (2*n+3) h
  have gc1:=gp0_C_tail d a m (2*n+2) h1
  have gc0:=gp0_C_tail d a m (2*n+1) h0
  have gt' : Trans.Recal.gp0 (C d a m) ((2*n+3+2:Nat):Int)=(a+n+1:Nat) := by
    simpa only [show (a+(2*n+3)/2:Nat)=a+n+1 by omega] using gt
  have gc1' : Trans.Recal.gp0 (C d a m) ((2*n+2+2:Nat):Int)=(a+n+1:Nat) := by
    simpa only [show (a+(2*n+2)/2:Nat)=a+n+1 by omega] using gc1
  have gc0' : Trans.Recal.gp0 (C d a m) ((2*n+1+2:Nat):Int)=(a+n:Nat) := by
    simpa only [show (a+(2*n+1)/2:Nat)=a+n by omega] using gc0
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega),if_pos (by rfl),length_C]
  rw [show ((2*n+3+2:Nat):Int)-1=((2*n+2+2:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2+1) (C d a m)
    (Trans.Recal.gp0 (C d a m) ((2*n+3+2:Nat):Int))
    ((2*n+2+2:Nat):Int) 0=((2*n+1+2:Nat):Int)
  rw [gt']
  rw [show m+2+1=(m+2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show ((2*n+2+2:Nat):Int)-1=((2*n+1+2:Nat):Int) by omega]
  change (if ((2*n+2+2:Nat):Int)<0 then -1 else
    if Trans.Recal.gp0 (C d a m) ((2*n+2+2:Nat):Int)<(a+n+1:Nat)
      then ((2*n+2+2:Nat):Int) else
      Trans.Recal.fpar0Aux (m+2) (C d a m) (a+n+1:Nat)
        ((2*n+1+2:Nat):Int) 0)=_
  rw [if_neg (by omega),gc1',if_neg (by omega)]
  change (if ((2*n+1+2:Nat):Int)<0 then -1 else
    if Trans.Recal.gp0 (C d a m) ((2*n+1+2:Nat):Int)<(a+n+1:Nat)
      then ((2*n+1+2:Nat):Int) else _)=_
  rw [if_neg (by omega),gc0',if_pos (by omega)]

theorem fpar_C_pos (d a m k : Nat) (hd : 0<d) (hda : d<a)
    (hk0 : 0<k) (hk : k<m+2) :
    Trans.Recal.fpar (C d a m) 0 (k:Int) 0=(parentL k:Nat) := by
  match k with
  | 0 => omega
  | 1 => simpa [parentL] using fpar_C_one d a m hd
  | 2 => simpa [parentL] using fpar_C_two d a m hd hda (by omega)
  | 3 => simpa [parentL] using fpar_C_three d a m hd hda (by omega)
  | q+4 =>
    by_cases he:(q+2)%2=0
    · have heq:q+2=2*((q+2)/2):=by omega
      obtain ⟨n, hn⟩ : ∃ n, q+4=2*n+2+2 :=
        ⟨(q+2)/2-1,by omega⟩
      rw [hn] at hk ⊢
      rw [show parentL (2*n+2+2)=2*n+1+2 by simp [parentL,parentT]]
      exact fpar_C_tail_even d a m n hd hda (by omega)
    · have ho:(q+2)%2=1:=by omega
      obtain ⟨n, hn⟩ : ∃ n, q+4=2*n+3+2 :=
        ⟨(q+2)/2-1,by omega⟩
      rw [hn] at hk ⊢
      rw [show parentL (2*n+3+2)=2*n+1+2 by
        rw [show 2*n+3+2=(2*n+1)+4 by omega]
        simp only [parentL,parentT]
        rw [if_neg (by omega)]
        omega]
      exact fpar_C_tail_odd d a m n hd hda (by omega)

theorem isAncAux_C (d a m k : Nat) (hd : 0<d) (hda : d<a) : ∀ f : Nat,
    k<m+2 → k<f → Trans.Recal.isAncAux f (C d a m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f:Nat, k<m+2 → k<f →
    Trans.Recal.isAncAux f (C d a m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · have hkpos:0<k:=by omega
      rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_C_pos d a m k hd hda hkpos hkm]
      rw [show (((parentL k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hpk:=parentL_lt k hkpos
      exact ih (parentL k) hpk f
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf))

theorem isPrincipalP_C (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.isPrincipalP (C d a m)=true := by
  have ha:=isAncAux_C d a m (m+1) hd hda (m+3) (by omega) (by omega)
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (C d a m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C]
    simp]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_C]; omega),length_C]
  rw [lenI_C,show (m:Int)+2-1=((m+1:Nat):Int) by omega]
  exact ha

theorem lenI_K (d a m : Nat) : Trans.Recal.lenI (K d a m)=(m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_K]
  omega

theorem gp0_K_tail (d a m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (K d a m) ((k+1:Nat):Int)=((a+k/2:Nat):Int) := by
  show (if ((k+1:Nat):Int)<0 then 0 else
    ((K d a m).getD (k+1) (0,0)).1)=_
  rw [if_neg (by omega)]
  show ((A a m).getD k (0,0)).1=_
  rw [getD_A a m k hk]

theorem fpar_K_one (d a m : Nat) (hda : d<a) (hm : 0<m) :
    Trans.Recal.fpar (K d a m) 0 1 0=0 := by
  have hgt : Trans.Recal.gp0 (K d a m) 1=(a:Int) := by
    simpa using gp0_K_tail d a m 0 hm
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_K]; omega),if_pos (by rfl),length_K,
    show (1:Int)-1=0 by omega]
  change Trans.Recal.fpar0Aux (m+2) (K d a m)
    (Trans.Recal.gp0 (K d a m) 1) 0 0=0
  rw [hgt]
  change (if (0:Int)<0 then -1 else
    if Trans.Recal.gp0 (K d a m) 0<(a:Int) then 0 else _)=0
  rw [if_neg (by omega),show Trans.Recal.gp0 (K d a m) 0=(d:Int) from rfl,
    if_pos (by push_cast; omega)]

theorem fpar_K_two (d a m : Nat) (hda : d<a) (hm : 1<m) :
    Trans.Recal.fpar (K d a m) 0 2 0=0 := by
  have hgt : Trans.Recal.gp0 (K d a m) 2=(a:Int) := by
    simpa using gp0_K_tail d a m 1 (by omega)
  have hgp1 : Trans.Recal.gp0 (K d a m) 1=(a:Int) := by
    simpa using gp0_K_tail d a m 0 (by omega)
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_K]; omega),if_pos (by rfl),length_K,
    show (2:Int)-1=1 by omega]
  change Trans.Recal.fpar0Aux (m+2) (K d a m)
    (Trans.Recal.gp0 (K d a m) 2) 1 0=0
  rw [hgt]
  change (if (1:Int)<0 then -1 else
    if Trans.Recal.gp0 (K d a m) 1<(a:Int) then 1 else
      Trans.Recal.fpar0Aux (m+1) (K d a m) (a:Int) 0 0)=0
  rw [if_neg (by omega),hgp1,if_neg (by omega)]
  change (if (0:Int)<0 then -1 else
    if Trans.Recal.gp0 (K d a m) 0<(a:Int) then 0 else _)=0
  rw [if_neg (by omega),show Trans.Recal.gp0 (K d a m) 0=(d:Int) from rfl,
    if_pos (by push_cast; omega)]

theorem fpar_K_tail_even (d a m n : Nat) (h : 2*n+2<m) :
    Trans.Recal.fpar (K d a m) 0 ((2*n+2+1:Nat):Int) 0=
      ((2*n+1+1:Nat):Int) := by
  have h1:2*n+1<m:=by omega
  have gt:=gp0_K_tail d a m (2*n+2) h
  have gc:=gp0_K_tail d a m (2*n+1) h1
  have gt' : Trans.Recal.gp0 (K d a m) ((2*n+2+1:Nat):Int)=(a+n+1:Nat) := by
    simpa only [show (a+(2*n+2)/2:Nat)=a+n+1 by omega] using gt
  have gc' : Trans.Recal.gp0 (K d a m) ((2*n+1+1:Nat):Int)=(a+n:Nat) := by
    simpa only [show (a+(2*n+1)/2:Nat)=a+n by omega] using gc
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_K]; omega),if_pos (by rfl),length_K,
    show ((2*n+2+1:Nat):Int)-1=((2*n+1+1:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1+1) (K d a m)
    (Trans.Recal.gp0 (K d a m) ((2*n+2+1:Nat):Int))
    ((2*n+1+1:Nat):Int) 0=((2*n+1+1:Nat):Int)
  rw [gt']
  change (if ((2*n+1+1:Nat):Int)<0 then -1 else
    if Trans.Recal.gp0 (K d a m) ((2*n+1+1:Nat):Int)<(a+n+1:Nat)
      then ((2*n+1+1:Nat):Int) else _)=_
  rw [if_neg (by omega),gc',if_pos (by omega)]

theorem fpar_K_tail_odd (d a m n : Nat) (h : 2*n+3<m) :
    Trans.Recal.fpar (K d a m) 0 ((2*n+3+1:Nat):Int) 0=
      ((2*n+1+1:Nat):Int) := by
  have h1:2*n+2<m:=by omega
  have h0:2*n+1<m:=by omega
  have gt:=gp0_K_tail d a m (2*n+3) h
  have gc1:=gp0_K_tail d a m (2*n+2) h1
  have gc0:=gp0_K_tail d a m (2*n+1) h0
  have gt' : Trans.Recal.gp0 (K d a m) ((2*n+3+1:Nat):Int)=(a+n+1:Nat) := by
    simpa only [show (a+(2*n+3)/2:Nat)=a+n+1 by omega] using gt
  have gc1' : Trans.Recal.gp0 (K d a m) ((2*n+2+1:Nat):Int)=(a+n+1:Nat) := by
    simpa only [show (a+(2*n+2)/2:Nat)=a+n+1 by omega] using gc1
  have gc0' : Trans.Recal.gp0 (K d a m) ((2*n+1+1:Nat):Int)=(a+n:Nat) := by
    simpa only [show (a+(2*n+1)/2:Nat)=a+n by omega] using gc0
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_K]; omega),if_pos (by rfl),length_K,
    show ((2*n+3+1:Nat):Int)-1=((2*n+2+1:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1+1) (K d a m)
    (Trans.Recal.gp0 (K d a m) ((2*n+3+1:Nat):Int))
    ((2*n+2+1:Nat):Int) 0=((2*n+1+1:Nat):Int)
  rw [gt',show m+1+1=(m+1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show ((2*n+2+1:Nat):Int)-1=((2*n+1+1:Nat):Int) by omega]
  change (if ((2*n+2+1:Nat):Int)<0 then -1 else
    if Trans.Recal.gp0 (K d a m) ((2*n+2+1:Nat):Int)<(a+n+1:Nat)
      then ((2*n+2+1:Nat):Int) else
      Trans.Recal.fpar0Aux (m+1) (K d a m) (a+n+1:Nat)
        ((2*n+1+1:Nat):Int) 0)=_
  rw [if_neg (by omega),gc1',if_neg (by omega)]
  change (if ((2*n+1+1:Nat):Int)<0 then -1 else
    if Trans.Recal.gp0 (K d a m) ((2*n+1+1:Nat):Int)<(a+n+1:Nat)
      then ((2*n+1+1:Nat):Int) else _)=_
  rw [if_neg (by omega),gc0',if_pos (by omega)]

theorem fpar_K_pos (d a m k : Nat) (hda : d<a) (hk0 : 0<k) (hk : k<m+1) :
    Trans.Recal.fpar (K d a m) 0 (k:Int) 0=(parentT k:Nat) := by
  match k with
  | 0 => omega
  | 1 => simpa [parentT] using fpar_K_one d a m hda (by omega)
  | 2 => simpa [parentT] using fpar_K_two d a m hda (by omega)
  | q+3 =>
    by_cases he:(q+2)%2=0
    · obtain ⟨n,hn⟩ : ∃ n,q+3=2*n+2+1 := ⟨(q+2)/2-1,by omega⟩
      rw [hn] at hk ⊢
      rw [show parentT (2*n+2+1)=2*n+1+1 by
        unfold parentT
        rw [if_pos (by omega)]
        omega]
      exact fpar_K_tail_even d a m n (by omega)
    · obtain ⟨n,hn⟩ : ∃ n,q+3=2*n+3+1 := ⟨(q+2)/2-1,by omega⟩
      rw [hn] at hk ⊢
      rw [show parentT (2*n+3+1)=2*n+1+1 by
        rw [show 2*n+3+1=2*n+2+2 by omega]
        unfold parentT
        rw [if_neg (by omega)]
        omega]
      exact fpar_K_tail_odd d a m n (by omega)

theorem isAncAux_K (d a m k : Nat) (hda : d<a) : ∀ f : Nat,
    k<m+1 → k<f → Trans.Recal.isAncAux f (K d a m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f:Nat, k<m+1 → k<f →
    Trans.Recal.isAncAux f (K d a m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · have hkpos:0<k:=by omega
      rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_K_pos d a m k hda hkpos hkm]
      rw [show (((parentT k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk f
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf))

theorem isPrincipalP_K (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.isPrincipalP (K d a m)=true := by
  have ha:=isAncAux_K d a m m hda (m+2) (by omega) (by omega)
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (K d a m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K]
    cases m <;> rfl]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_K]; omega),length_K]
  rw [lenI_K,show (m:Int)+1-1=(m:Int) by omega]
  exact ha

theorem fpar0_eq_fpar_row0 (P : Trans.Recal.PS) (j k : Int)
    (hv : ¬(j<0 ∨ j≥Trans.Recal.lenI P)) :
    Trans.Recal.fpar0 P j k=Trans.Recal.fpar P 0 j k := by
  unfold Trans.Recal.fpar0 Trans.Recal.fpar
  rw [if_neg hv,if_neg hv,if_pos (by rfl)]

theorem fpar0_C_one (d a m : Nat) (hd : 0<d) :
    Trans.Recal.fpar0 (C d a m) 1 0=0 := by
  rw [fpar0_eq_fpar_row0 _ _ _ (by rw [lenI_C]; omega)]
  exact fpar_C_one d a m hd

theorem fpar0_C_two (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 0<m) :
    Trans.Recal.fpar0 (C d a m) 2 1=1 := by
  have hgt : Trans.Recal.gp0 (C d a m) 2=(a:Int) := by
    simpa using gp0_C_tail d a m 0 hm
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_C]; omega),length_C,show (2:Int)-1=1 by omega]
  change Trans.Recal.fpar0Aux (m+2+1) (C d a m)
    (Trans.Recal.gp0 (C d a m) 2) 1 1=1
  rw [hgt]
  change (if (1:Int)<1 then -1 else
    if Trans.Recal.gp0 (C d a m) 1<(a:Int) then 1 else _)=1
  rw [if_neg (by omega),show Trans.Recal.gp0 (C d a m) 1=(d:Int) from rfl,
    if_pos (by push_cast; omega)]

theorem fpar0_C_three_lb (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 1<m) :
    Trans.Recal.fpar0 (C d a m) 3 2=-1 := by
  have hgt : Trans.Recal.gp0 (C d a m) 3=(a:Int) := by
    simpa using gp0_C_tail d a m 1 (by omega)
  have hgp2 : Trans.Recal.gp0 (C d a m) 2=(a:Int) := by
    simpa using gp0_C_tail d a m 0 (by omega)
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_C]; omega),length_C,show (3:Int)-1=2 by omega]
  change Trans.Recal.fpar0Aux (m+2+1) (C d a m)
    (Trans.Recal.gp0 (C d a m) 3) 2 2=-1
  rw [hgt]
  change (if (2:Int)<2 then -1 else
    if Trans.Recal.gp0 (C d a m) 2<(a:Int) then 2 else
      Trans.Recal.fpar0Aux (m+2) (C d a m) (a:Int) 1 2)=-1
  rw [if_neg (by omega),hgp2,if_neg (by omega)]
  change (if (1:Int)<2 then -1 else _)=-1
  rw [if_pos (by omega)]

theorem fpar0_C_three_zero (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 1<m) :
    Trans.Recal.fpar0 (C d a m) 3 0=1 := by
  rw [fpar0_eq_fpar_row0 _ _ _ (by rw [lenI_C]; omega)]
  exact fpar_C_three d a m hd hda hm

theorem fpar1_C_one (d a m : Nat) (hd : 0<d) :
    Trans.Recal.fpar (C d a m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [show Trans.Recal.gp1 (C d a m) 1=1 from rfl,length_C]
  rw [show m+2+1=(m+2)+1 by omega,Trans.Recal.fpar1Aux]
  rw [fpar0_C_one d a m hd,if_neg (by omega),
    show Trans.Recal.gp1 (C d a m) 0=0 from rfl,if_pos (by omega)]

theorem fpar1_C_two (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 0<m) :
    Trans.Recal.fpar (C d a m) 1 2 1=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [show Trans.Recal.gp1 (C d a m) 2=2 from by
    simpa using gp1_C_tail d a m 0 hm,length_C]
  rw [show m+2+1=(m+2)+1 by omega,Trans.Recal.fpar1Aux]
  rw [fpar0_C_two d a m hd hda hm,if_neg (by omega),
    show Trans.Recal.gp1 (C d a m) 1=1 from rfl,if_pos (by omega)]

theorem fpar1_C_three_lb (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 1<m) :
    Trans.Recal.fpar (C d a m) 1 3 2=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [show Trans.Recal.gp1 (C d a m) 3=1 from by
    simpa using gp1_C_tail d a m 1 hm,length_C]
  rw [show m+2+1=(m+2)+1 by omega,Trans.Recal.fpar1Aux]
  rw [fpar0_C_three_lb d a m hd hda hm,if_pos (by omega)]

theorem isParentP_C_one (d a m : Nat) (hd : 0<d) :
    Trans.Recal.isParentP (C d a m) 1 1 0=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_C_one d a m hd,lenI_C]
  rw [show decide ((0:Int)<(m:Int)+2)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_C_two (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 0<m) :
    Trans.Recal.isParentP (C d a m) 1 2 1=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_C_two d a m hd hda hm,lenI_C]
  rw [show decide ((1:Int)<(m:Int)+2)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_C_three (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 1<m) :
    Trans.Recal.isParentP (C d a m) 1 3 2=false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_C_three_lb d a m hd hda hm]
  simp

theorem trMax_C_zero (d a : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.trMax (C d a 0)=1 := by
  show Trans.Recal.trMaxAux ((C d a 0).length+1) (C d a 0) 0=1
  rw [length_C,Trans.Recal.trMaxAux,if_neg (by rw [lenI_C]; omega),
    show (0:Int)+1=1 by omega,
    isParentP_C_one d a 0 hd]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_C d a 0]; omega)]
  rw [show (1:Int)+1=2 by omega]
  rw [show Trans.Recal.isParentP (C d a 0) 1 2 1=false from by
    unfold Trans.Recal.isParentP Trans.Recal.fpar
    rw [show decide ((0:Int)≤1)=true from decide_eq_true (by omega),
      show decide ((1:Int)<Trans.Recal.lenI (C d a 0))=true from
        decide_eq_true (by rw [lenI_C d a 0]; omega)]
    simp only [Bool.true_and]
    rw [if_pos (by rw [lenI_C d a 0]; omega)]
    rfl]
  rfl

theorem trMax_C_one (d a : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.trMax (C d a 1)=2 := by
  show Trans.Recal.trMaxAux ((C d a 1).length+1) (C d a 1) 0=2
  rw [length_C,Trans.Recal.trMaxAux,if_neg (by rw [lenI_C]; omega),
    show (0:Int)+1=1 by omega,
    isParentP_C_one d a 1 hd]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_C]; omega),
    show (1:Int)+1=2 by omega,
    isParentP_C_two d a 1 hd hda (by omega)]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_C d a 1]; omega)]
  rw [show (2:Int)+1=3 by omega]
  rw [show Trans.Recal.isParentP (C d a 1) 1 3 2=false from by
    unfold Trans.Recal.isParentP Trans.Recal.fpar
    rw [show decide ((0:Int)≤2)=true from decide_eq_true (by omega),
      show decide ((2:Int)<Trans.Recal.lenI (C d a 1))=true from
        decide_eq_true (by rw [lenI_C d a 1]; omega)]
    simp only [Bool.true_and]
    rw [if_pos (by rw [lenI_C d a 1]; omega)]
    rfl]
  rfl

theorem trMax_C_add_two (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.trMax (C d a (m+2))=2 := by
  show Trans.Recal.trMaxAux ((C d a (m+2)).length+1) (C d a (m+2)) 0=2
  rw [length_C,Trans.Recal.trMaxAux,if_neg (by rw [lenI_C]; omega),
    show (0:Int)+1=1 by omega,
    isParentP_C_one d a (m+2) hd]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_C]; omega),
    show (1:Int)+1=2 by omega,
    isParentP_C_two d a (m+2) hd hda (by omega)]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Trans.Recal.trMaxAux,if_neg (by rw [lenI_C]; omega),
    show (2:Int)+1=3 by omega,
    isParentP_C_three d a (m+2) hd hda (by omega)]
  rfl

theorem fpar_K_zero (d a m : Nat) :
    Trans.Recal.fpar (K d a m) 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_K]; omega),if_pos (by rfl),length_K]
  rw [Trans.Recal.fpar0Aux,if_pos (by omega)]

theorem fAncAux_K_last (d a m k : Nat) (hda : d<a) : ∀ (f : Nat)
    (acc : List Int), k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (K d a m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ (f:Nat) (acc:List Int),
    k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (K d a m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      rw [show ((0:Nat):Int)=0 from rfl,fpar_K_zero,if_neg (by omega)]
      exact hlast
    · have hkpos:0<k:=by omega
      rw [fpar_K_pos d a m k hda hkpos hkm,if_pos (by omega)]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk f (acc++[((parentT k:Nat):Int)])
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf)) (by simp)

theorem fAnc_K_last (d a m : Nat) (hda : d<a) :
    (Trans.Recal.fAnc (K d a m) 0 (m:Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_K]; omega),length_K]
  exact fAncAux_K_last d a m m hda (m+2) [(m:Int)]
    (by omega) (by omega) (by simp)

theorem slice_K_full (d a m : Nat) :
    Trans.Recal.slice (K d a m) 0 ((m:Int)+1)=K d a m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show (((m:Int)+1)-0).toNat=m+1 by omega]
  simpa only [length_K] using (List.take_length (l:=K d a m))

theorem ppair_K (d a m : Nat) (hda : d<a) :
    Trans.Recal.ppair (K d a m)=[K d a m] := by
  unfold Trans.Recal.ppair
  rw [length_K,lenI_K,Trans.Recal.ppairAux]
  dsimp only
  rw [show (m:Int)+1-1=(m:Int) by omega,if_neg (by omega),
    fAnc_K_last d a m hda]
  simp only [Option.getD_some]
  rw [show (0:Int)-1=-1 by omega,Trans.Recal.ppairAux,if_pos (by omega),
    slice_K_full]

theorem A_add_two (a m : Nat) :
    A a (m+2)=
      [(((a:Nat):Int),(2:Int)),(((a:Nat):Int),(1:Int))] ++ A (a+1) m := by
  unfold A
  rw [show m+2=2+m by omega,List.range_add,List.map_append]
  rw [show List.range 2=[0,1] by rfl]
  simp only [List.map_cons,List.map_nil,List.append_nil,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  apply Prod.ext <;> simp <;> push_cast <;> omega

theorem drop_three_C_add_two (d a m : Nat) :
    (C d a (m+2)).drop 3=K a (a+1) m := by
  rw [C,K,A_add_two]
  rfl

theorem brF_C_add_two (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.brF (C d a (m+2))=[K a (a+1) m] := by
  unfold Trans.Recal.brF
  rw [trMax_C_add_two d a m hd hda]
  rw [show ((2:Int)+1).toNat=3 by rfl,drop_three_C_add_two]
  exact ppair_K a (a+1) m (by omega)

theorem firstNodes_C_add_two (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.firstNodes (C d a (m+2))=[3,((m+4:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_C_add_two d a m hd hda,trMax_C_add_two d a m hd hda]
  simp [length_K]
  omega

theorem joints_C_add_two (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.joints (C d a (m+2))=[1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_C_add_two d a m hd hda]
  change [Trans.Recal.fpar (C d a (m+2)) 0 3 0]=[1]
  rw [fpar_C_three d a (m+2) hd hda (by omega)]

theorem fpar1_C_three_zero (d a m : Nat) (hd : 0<d) (hda : d<a) (hm : 1<m) :
    Trans.Recal.fpar (C d a m) 1 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [show Trans.Recal.gp1 (C d a m) 3=1 from by
    simpa using gp1_C_tail d a m 1 hm,length_C]
  rw [show m+2+1=(m+2)+1 by omega,Trans.Recal.fpar1Aux]
  rw [fpar0_C_three_zero d a m hd hda hm,if_neg (by omega),
    show Trans.Recal.gp1 (C d a m) 1=1 from rfl,if_neg (by omega)]
  rw [Trans.Recal.fpar1Aux]
  rw [fpar0_C_one d a m hd,if_neg (by omega),
    show Trans.Recal.gp1 (C d a m) 0=0 from rfl,if_pos (by omega)]

theorem A_zero (a : Nat) : A a 0=[] := rfl

theorem K_zero (d a : Nat) : K d a 0=[(((d:Nat):Int),(1:Int))] := rfl

theorem C_zero (d a : Nat) : C d a 0=[(0,0),(((d:Nat):Int),(1:Int))] := rfl

theorem A_one (a : Nat) : A a 1=[(((a:Nat):Int),(2:Int))] := by
  unfold A
  rfl

theorem C_one (d a : Nat) :
    C d a 1=[(0,0),(((d:Nat):Int),(1:Int)),(((a:Nat):Int),(2:Int))] := by
  rw [C,K,A_one]

theorem incrFirst_A (a m r : Nat) :
    Trans.Recal.incrFirst (A a m) (r:Int)=A (a+r) m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext <;> simp
  push_cast
  omega

theorem incrFirst_K (d a m r : Nat) :
    Trans.Recal.incrFirst (K d a m) (r:Int)=K (d+r) (a+r) m := by
  unfold Trans.Recal.incrFirst K
  rw [List.map_cons]
  change ((d:Int)+(r:Int),1)::Trans.Recal.incrFirst (A a m) (r:Int)=_
  rw [incrFirst_A]
  congr 1

def KRed : Nat → Trans.Recal.PS
  | 0 => [(1,1)]
  | m+1 => (1,1)::(2,2)::T m

def CRed (m : Nat) : Trans.Recal.PS := (0,0)::KRed m

theorem incrFirst_KRed (m : Nat) :
    Trans.Recal.incrFirst (KRed m) 1=T (m+1) := by
  cases m with
  | zero => rfl
  | succ m =>
    unfold KRed T Trans.Recal.incrFirst
    rw [show m+2=2+m by omega,List.range_add]
    rw [show List.range 2=[0,1] by rfl]
    simp only [List.map_cons,List.map_nil,List.map_append,List.map_map]
    congr 1
    change (3,2)::List.map ((fun c => (c.1+1,c.2)) ∘
        fun k => (((((k+5)/2:Nat):Int)),((((k%2)+1:Nat):Int)))) (List.range m)=
      (3,2)::List.map ((fun k => (((((k+5)/2:Nat):Int)),
        ((((k%2)+1:Nat):Int)))) ∘ fun x => 2+x) (List.range m)
    congr 1
    apply List.map_congr_left
    intro k _
    apply Prod.ext <;> simp <;> push_cast <;> omega

theorem A_two_succ (m : Nat) : A 2 (m+1)=(2,2)::T m := by
  unfold A T
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  apply Prod.ext <;> simp <;> push_cast <;> omega

theorem KRed_eq_K (m : Nat) : KRed m=K 1 2 m := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [KRed,K,A_two_succ]
    rfl

theorem CRed_eq_C (m : Nat) : CRed m=C 1 2 m := by
  rw [CRed,C,KRed_eq_K]


theorem red_C_zero (d a f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (f+1) (C d a 0)=CRed 0 := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C d a 0)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C]
    simp,
    isPrincipalP_C d a 0 hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (C d a 0) 0==0 &&
      Trans.Recal.gp1 (C d a 0) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_C_zero d a hd hda,lenI_C]
  rfl

theorem red_C_one (d a f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (f+1) (C d a 1)=CRed 1 := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C d a 1)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C]
    simp,
    isPrincipalP_C d a 1 hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (C d a 1) 0==0 &&
      Trans.Recal.gp1 (C d a 1) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_C_one d a hd hda,lenI_C]
  rfl

theorem red_K_from_C (d a m f : Nat) (hd : 0<d) (hda : d<a)
    (hC : Trans.Recal.red (f+1) (C (d+1) (a+1) m)=CRed m) :
    Trans.Recal.red (f+2) (K d a m)=KRed m := by
  rw [show f+2=(f+1)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d a m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K]
    cases m <;> rfl,
    isPrincipalP_K d a m hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K d a m) 0==0 &&
      Trans.Recal.gp1 (K d a m) 0==0)=false from by
    change (((d:Int)==0) && ((1:Int)==0))=false
    rw [show ((d:Int)==0)=false from beq_eq_false_iff_ne.mpr (by omega)]
    rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (K d a m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Recal.jjSeq 0 (Trans.Recal.gp1 (K d a m) 0-1) ++
      Trans.Recal.incrFirst (K d a m) (Trans.Recal.gp1 (K d a m) 0)=
      C (d+1) (a+1) m from by
    rw [show Trans.Recal.gp1 (K d a m) 0=1 from rfl]
    change [(0,0)]++Trans.Recal.incrFirst (K d a m) 1=_
    rw [show Trans.Recal.incrFirst (K d a m) 1=K (d+1) (a+1) m from by
      simpa using incrFirst_K d a m 1]
    rfl,hC]
  rw [show Trans.Recal.lenI (CRed m)-1=(m:Int)+1 from by
    rw [CRed_eq_C,lenI_C]
    omega]
  rw [show Trans.Recal.gp1 (K d a m) 0=1 from rfl,
    show decide ((1:Int)≤(m:Int)+1)=true from decide_eq_true (by omega)]
  rw [show (CRed m).drop (1:Int).toNat=KRed m from by rfl,
    show Trans.Recal.isPrincipalP (KRed m)=true from by
      rw [KRed_eq_K]
      exact isPrincipalP_K 1 2 m (by omega) (by omega)]
  simp only [Bool.true_and,if_true]
  rw [show -Trans.Recal.gp0 (CRed m) 1+
      Trans.Recal.gp1 (CRed m) 1=0 from by rw [CRed_eq_C]; rfl]
  simp [Trans.Recal.incrFirst]

theorem red_C_step (d a m f : Nat) (hd : 0<d) (hda : d<a)
    (hK : Trans.Recal.red (2*m+(f+2)+2) (K 2 (a+1) m)=KRed m) :
    Trans.Recal.red (2*(m+2)+f+1) (C d a (m+2))=CRed (m+2) := by
  rw [show 2*(m+2)+f+1=(2*m+(f+2)+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C d a (m+2))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C d a (m+2)]
    simp,
    isPrincipalP_C d a (m+2) hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (C d a (m+2)) 0==0 &&
      Trans.Recal.gp1 (C d a (m+2)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_C_add_two d a m hd hda]
  rw [show Trans.Recal.lenI (C d a (m+2))-1=(m:Int)+3 from by
    rw [lenI_C d a (m+2)]
    omega]
  rw [show ((2:Int)==(m:Int)+3)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_C_add_two d a m hd hda,firstNodes_C_add_two d a m hd hda,
    joints_C_add_two d a m hd hda]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([K a (a+1) m] : List Trans.Recal.PS).getD 0 []=K a (a+1) m from rfl,
    show ([3,((m+4:Nat):Int)] : List Int).getD 0 0=3 from rfl,
    show ([1] : List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (K a (a+1) m) 0=1 from rfl]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [fpar1_C_three_zero d a (m+2) hd hda (by omega)]
  change Trans.Recal.jjSeq 0 2 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (2*m+(f+2)+2) ((2,1)::Trans.Recal.derp (K a (a+1) m))) 1=_
  change Trans.Recal.jjSeq 0 2 ++
    Trans.Recal.incrFirst (Trans.Recal.red (2*m+(f+2)+2) (K 2 (a+1) m)) 1=_
  rw [hK,incrFirst_KRed]
  rfl


theorem red_C_all : ∀ m d a f : Nat, 0<d → d<a →
    Trans.Recal.red (2*m+f+1) (C d a m)=CRed m := by
  intro m
  refine Nat.strongRecOn (motive:=fun m => ∀ d a f:Nat, 0<d → d<a →
    Trans.Recal.red (2*m+f+1) (C d a m)=CRed m) m ?_
  intro m ih d a f hd hda
  cases m with
  | zero =>
    rw [show 2*0+f+1=f+1 by omega]
    exact red_C_zero d a f hd hda
  | succ p =>
    cases p with
    | zero =>
      rw [show 2*1+f+1=f+3 by omega]
      exact red_C_one d a (f+2) hd hda
    | succ q =>
      have hc : Trans.Recal.red (2*q+(f+2)+1) (C 3 (a+2) q)=CRed q :=
        ih q (by omega) 3 (a+2) (f+2) (by omega) (by omega)
      have hk : Trans.Recal.red (2*q+(f+2)+2) (K 2 (a+1) q)=KRed q :=
        red_K_from_C 2 (a+1) q (2*q+(f+2)) (by omega) (by omega) hc
      exact red_C_step d a q f hd hda hk

theorem red_K_all (d a m f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (2*m+f+2) (K d a m)=KRed m := by
  apply red_K_from_C d a m (2*m+f) hd hda
  exact red_C_all m (d+1) (a+1) f (by omega) (by omega)

theorem T_succ_eq_K (m : Nat) : T (m+1)=K 2 3 m := by
  unfold T K A
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  apply Prod.ext <;> simp <;> push_cast <;> omega

theorem red_T_succ (m f : Nat) :
    Trans.Recal.red (2*m+f+2) (T (m+1))=KRed m := by
  rw [T_succ_eq_K]
  exact red_K_all 2 3 m f (by omega) (by omega)

theorem red_L_zero (f : Nat) : Trans.Recal.red (f+1) (L 0)=L 0 := by
  rw [Trans.Recal.red]
  rfl

theorem red_L_succ (m f : Nat) :
    Trans.Recal.red (2*m+f+3) (L (m+1))=L (m+1) := by
  rw [show 2*m+f+3=(2*m+f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L (m+1))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_L]
    simp,
    isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L (m+1)) 0==0 &&
      Trans.Recal.gp1 (L (m+1)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L,lenI_L]
  rw [show ((2:Int)==(((m+1:Nat):Int)+3-1))=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L_succ,firstNodes_L_succ,joints_L_succ]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([T (m+1)] : List Trans.Recal.PS).getD 0 []=T (m+1) from rfl,
    show ([3,((m+4:Nat):Int)] : List Int).getD 0 0=3 from rfl,
    show ([1] : List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (T (m+1)) 0=1 from by
    simpa using gp1_T (m+1) 0 (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [fpar1_L_three_zero]
  change Trans.Recal.jjSeq 0 2 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (2*m+f+2) ((2,1)::Trans.Recal.derp (T (m+1)))) 1=_
  rw [show (2,1)::Trans.Recal.derp (T (m+1))=T (m+1) from by
    rw [T_succ_eq_K]
    rfl,red_T_succ,incrFirst_KRed]
  rfl

theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  unfold Trans.Recal.redP
  cases m with
  | zero =>
    have hb : 1≤Trans.Recal.redFuel (L 0) := by
      unfold Trans.Recal.redFuel
      omega
    rw [show Trans.Recal.redFuel (L 0)=(Trans.Recal.redFuel (L 0)-1)+1 by omega]
    exact red_L_zero _
  | succ m =>
    have hb : 2*m+3≤Trans.Recal.redFuel (L (m+1)) := by
      unfold Trans.Recal.redFuel
      rw [length_L]
      omega
    rw [show Trans.Recal.redFuel (L (m+1))=
      2*m+(Trans.Recal.redFuel (L (m+1))-2*m-3)+3 by omega]
    exact red_L_succ m _

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  exact G1.beq_PS_self _

/-! ### The alternating type-three/type-six reader steps. -/

abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev D1X : Trans.Dict.BT := .D 1 X

theorem LBT_zero : LBT 0=.D 0 X := rfl

theorem LBT_odd (n : Nat) : LBT (2*n+1)=.D 0 (W (n+2) .zero) := by
  rw [show 2*n+1=(2*n)+1 by omega,LBT,if_pos (by omega)]
  congr 2
  omega

theorem LBT_even (n : Nat) : LBT (2*n+2)=.D 0 (W (n+2) X) := by
  rw [show 2*n+2=(2*n+1)+1 by omega,LBT]
  rw [if_neg (by omega)]
  congr 2
  omega

theorem gp0_L_row1 (m n : Nat) (h : 2*n<m) :
    Trans.Recal.gp0 (L m) ((2*n+3:Nat):Int)=(n+2:Nat) := by
  simpa only [show (2*n+5)/2=n+2 by omega] using gp0_L_tail m (2*n) h

theorem gp1_L_row1 (m n : Nat) (h : 2*n<m) :
    Trans.Recal.gp1 (L m) ((2*n+3:Nat):Int)=1 := by
  show (if ((2*n+3:Nat):Int)<0 then 0 else
    ((L m).getD (2*n+3) (0,0)).2)=1
  rw [if_neg (by omega),getD_L_tail m (2*n) h]
  simp

theorem gp0_L_before_row1 (m n : Nat) (h : 2*n<m) :
    Trans.Recal.gp0 (L m) ((2*n+2:Nat):Int)=(n+2:Nat) := by
  cases n with
  | zero => rfl
  | succ n =>
    simpa only [show (2*(n+1)+2:Nat)=2*n+4 by omega,
      show (n+1+2:Nat)=n+3 by omega,
      show (2*n+1+3:Nat)=2*n+4 by omega,
      show (2*n+1+5)/2=n+3 by omega] using
      gp0_L_tail m (2*n+1) (by omega)

theorem fpar0_L_row1_lb (m n : Nat) (h : 2*n<m) :
    Trans.Recal.fpar0 (L m) ((2*n+3:Nat):Int) ((2*n+2:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L_row1 m n h]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega)]
  rw [show ((2*n+3:Nat):Int)-1=((2*n+2:Nat):Int) by omega,
    gp0_L_before_row1 m n h,if_neg (by omega)]
  rw [Trans.Recal.fpar0Aux,if_pos (by omega)]

theorem fpar1_L_row1_lb (m n : Nat) (h : 2*n<m) :
    Trans.Recal.fpar (L m) 1 ((2*n+3:Nat):Int) ((2*n+2:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_row1 m n h,length_L]
  rw [Trans.Recal.fpar1Aux,fpar0_L_row1_lb m n h,if_pos (by omega)]

theorem isAdm_L_row1 (m n : Nat) (h : 2*n<m) :
    Trans.Recal.isAdm (L m) ((2*n+3:Nat):Int)=true := by
  have hp : Trans.Recal.isParentP (L m) 1 ((2*n+3:Nat):Int)
      ((2*n+2:Nat):Int)=false := by
    unfold Trans.Recal.isParentP
    rw [show decide (0≤((2*n+2:Nat):Int))=true from decide_eq_true (by omega),
      show decide (((2*n+2:Nat):Int)<Trans.Recal.lenI (L m))=true from
        decide_eq_true (by rw [lenI_L]; omega)]
    simp only [Bool.true_and]
    rw [fpar1_L_row1_lb m n h]
    exact decide_eq_false (by omega)
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((2*n+3:Nat):Int)>Trans.Recal.lenI (L m))=false from by
    apply decide_eq_false
    rw [lenI_L]
    omega]
  simp only [Bool.false_or]
  rw [show ((2*n+3:Nat):Int)-1=((2*n+2:Nat):Int) by omega,hp,
    Bool.false_and]
  rfl

theorem adm_L_row1 (m n : Nat) (h : 2*n<m) :
    Trans.Recal.adm (L m) ((2*n+3:Nat):Int)=((2*n+3:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L,Trans.Recal.admAux,if_neg (by omega),isAdm_L_row1 m n h,if_pos rfl]

theorem gp1_L_even_top (n : Nat) :
    Trans.Recal.gp1 (L (2*n+2)) ((2*n+4:Nat):Int)=2 := by
  show (if ((2*n+4:Nat):Int)<0 then 0 else
    ((L (2*n+2)).getD (2*n+4) (0,0)).2)=2
  rw [if_neg (by omega),show 2*n+4=2*n+1+3 by omega,
    getD_L_tail (2*n+2) (2*n+1) (by omega)]
  simp

theorem gp1_L_odd_top (n : Nat) :
    Trans.Recal.gp1 (L (2*n+3)) ((2*n+5:Nat):Int)=1 := by
  simpa only [show 2*n+5=2*(n+1)+3 by omega] using
    gp1_L_row1 (2*n+3) (n+1) (by omega)

theorem fpar_L_even_top (n : Nat) :
    Trans.Recal.fpar (L (2*n+2)) 0 ((2*n+4:Nat):Int) 0=
      ((2*n+3:Nat):Int) := by
  simpa only [show 2*n+1+3=2*n+4 by omega] using
    fpar_L_tail_odd (2*n+2) n (by omega)

theorem fpar_L_odd_top (n : Nat) :
    Trans.Recal.fpar (L (2*n+3)) 0 ((2*n+5:Nat):Int) 0=
      ((2*n+3:Nat):Int) := by
  simpa only [show 2*n+2+3=2*n+5 by omega] using
    fpar_L_tail_even (2*n+3) n (by omega)

theorem transType_L_even (n : Nat) :
    Trans.Recal.transTypeMain (L (2*n+2)) ((2*n+3:Nat):Int)
      ((2*n+4:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_even_top,gp1_L_row1 (2*n+2) n (by omega)]
  simp only [show ((2:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [if_neg (by omega),if_neg (by omega)]

theorem transType_L_odd (n : Nat) :
    Trans.Recal.transTypeMain (L (2*n+3)) ((2*n+3:Nat):Int)
      ((2*n+5:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_odd_top,gp1_L_row1 (2*n+3) n (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [if_pos (by omega),isAdm_L_row1 (2*n+3) n (by omega),if_pos rfl]

theorem mkC2_L_even (n : Nat) :
    Trans.Recal.mkC2 (L (2*n+2)) ((2*n+3:Nat):Int)
      ((2*n+4:Nat):Int) 6 D1z=D1X := by
  show Trans.Dict.BT.D 1 (.D
    (Trans.Recal.gp1 (L (2*n+2)) ((2*n+4:Nat):Int)).toNat .zero)=D1X
  rw [gp1_L_even_top]
  rfl

theorem mkC2_L_odd (n : Nat) :
    Trans.Recal.mkC2 (L (2*n+3)) ((2*n+3:Nat):Int)
      ((2*n+5:Nat):Int) 3 D1X=.D 1 (W 1 .zero) := by
  show Trans.Dict.BT.D 1 (Trans.Recal.bplus X (.D
    (Trans.Recal.gp1 (L (2*n+3)) ((2*n+5:Nat):Int)).toNat .zero))=
      .D 1 (W 1 .zero)
  rw [gp1_L_odd_top]
  rfl

theorem adm_L_one : Trans.Recal.adm (L 1) 1=0 := by rfl
theorem transType_L_one : Trans.Recal.transTypeMain (L 1) 1 3=4 := by rfl
theorem mkC2_L_one :
    Trans.Recal.mkC2 (L 1) 1 3 4 (LBT 0)=LBT 1 := by rfl

theorem toL_W_succ (k : Nat) (b : Trans.Dict.BT) :
    (W (k+1) b).toL=[X,.D 1 (W k b)] := by rfl

theorem repl_W_zero : ∀ (k f : Nat), 2*k+2≤f →
    Trans.Recal.replMark f (W (k+1) .zero) D1z D1X=
      some (W (k+1) X)
  | 0, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+2 := ⟨f-2,by omega⟩
    change Trans.Recal.replMark (g+2) (Trans.Dict.BT.sum X D1z) D1z D1X=
      some (Trans.Dict.BT.sum X D1X)
    rw [Trans.Recal.replMark]
    change (Trans.Recal.replMark (g+1) D1z D1z D1X).map
      (fun q => Trans.Dict.BT.sum X q)=some (Trans.Dict.BT.sum X D1X)
    rw [Trans.Recal.replMark,if_pos (G1.beq_BT_self D1z)]
    rfl
  | k+1, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+2 := ⟨f-2,by omega⟩
    change Trans.Recal.replMark (g+2) (Trans.Dict.BT.sum X (.D 1 (W (k+1) .zero)))
      D1z D1X=some (Trans.Dict.BT.sum X (.D 1 (W (k+1) X)))
    rw [Trans.Recal.replMark]
    change (Trans.Recal.replMark (g+1) (.D 1 (W (k+1) .zero)) D1z D1X).map
      (fun q => Trans.Dict.BT.sum X q)=
        some (Trans.Dict.BT.sum X (.D 1 (W (k+1) X)))
    rw [Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (W (k+1) .zero))==D1z)=false from by
        rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [repl_W_zero k g (by omega)]
    rfl

theorem repl_W_X : ∀ (k f : Nat), 2*k+2≤f →
    Trans.Recal.replMark f (W (k+1) X) D1X (.D 1 (W 1 .zero))=
      some (W (k+2) .zero)
  | 0, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+2 := ⟨f-2,by omega⟩
    change Trans.Recal.replMark (g+2) (Trans.Dict.BT.sum X D1X) D1X
      (.D 1 (W 1 .zero))=some (Trans.Dict.BT.sum X (.D 1 (W 1 .zero)))
    rw [Trans.Recal.replMark]
    change (Trans.Recal.replMark (g+1) D1X D1X (.D 1 (W 1 .zero))).map
      (fun q => Trans.Dict.BT.sum X q)=
        some (Trans.Dict.BT.sum X (.D 1 (W 1 .zero)))
    rw [Trans.Recal.replMark,if_pos (G1.beq_BT_self D1X)]
    rfl
  | k+1, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+2 := ⟨f-2,by omega⟩
    change Trans.Recal.replMark (g+2) (Trans.Dict.BT.sum X (.D 1 (W (k+1) X))) D1X
      (.D 1 (W 1 .zero))=
        some (Trans.Dict.BT.sum X (.D 1 (W (k+2) .zero)))
    rw [Trans.Recal.replMark]
    change (Trans.Recal.replMark (g+1) (.D 1 (W (k+1) X)) D1X
      (.D 1 (W 1 .zero))).map (fun q => Trans.Dict.BT.sum X q)=
        some (Trans.Dict.BT.sum X (.D 1 (W (k+2) .zero)))
    rw [Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (W (k+1) X))==D1X)=false from by
        rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [repl_W_X k g (by omega)]
    rfl

theorem repl_LBT_odd (f n : Nat) (hf : 2*n+6≤f) :
    Trans.Recal.replMark f (LBT (2*n+1)) D1z D1X=
      some (LBT (2*n+2)) := by
  rw [LBT_odd,LBT_even]
  cases f with
  | zero => omega
  | succ f =>
    rw [Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (W (n+2) .zero))==D1z)=false from by
      cases n <;> rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [repl_W_zero (n+1) f (by omega)]
    rfl

theorem repl_LBT_even (f n : Nat) (hf : 2*n+6≤f) :
    Trans.Recal.replMark f (LBT (2*n+2)) D1X (.D 1 (W 1 .zero))=
      some (LBT (2*n+3)) := by
  rw [LBT_even]
  rw [show 2*n+3=2*(n+1)+1 by omega,LBT_odd]
  cases f with
  | zero => omega
  | succ f =>
    rw [Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (W (n+2) X))==D1X)=false from by
      cases n <;> rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [repl_W_X (n+1) f (by omega)]
    rfl

/-! ### Memo invariant. -/

def Allowed : Nat → Option Int → Prop
  | 0, req => req=none ∨ req=some 0
  | k+1, req => if k%2=0 then
      req=none ∨ req=some ((k+3:Nat):Int)
    else req=none ∨ req=some ((k+2:Nat):Int) ∨
      req=some ((k+3:Nat):Int)

def Val : Nat → Option Int → Trans.Dict.BT
  | 0, _ => LBT 0
  | k+1, req => if req=none then LBT (k+1)
      else if k%2=0 then D1z
      else if req=some ((k+2:Nat):Int) then D1X else X

theorem Allowed_none (k : Nat) : Allowed k none := by
  cases k <;> simp [Allowed]

theorem Val_none (k : Nat) : Val k none=LBT k := by
  cases k <;> simp [Val]

theorem Allowed_zero_mark : Allowed 0 (some 0) := Or.inr rfl

theorem Allowed_odd_top (n : Nat) :
    Allowed (2*n+1) (some ((2*n+3:Nat):Int)) := by
  simp [Allowed]

theorem Val_odd_top (n : Nat) :
    Val (2*n+1) (some ((2*n+3:Nat):Int))=D1z := by
  simp [Val]

theorem Allowed_even_own (n : Nat) :
    Allowed (2*n+2) (some ((2*n+3:Nat):Int)) := by
  rw [show 2*n+2=(2*n+1)+1 by omega,Allowed,if_neg (by omega)]
  exact Or.inr (Or.inl (by congr 2 <;> omega))

theorem Allowed_even_top (n : Nat) :
    Allowed (2*n+2) (some ((2*n+4:Nat):Int)) := by
  rw [show 2*n+2=(2*n+1)+1 by omega,Allowed,if_neg (by omega)]
  exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Val_even_own (n : Nat) :
    Val (2*n+2) (some ((2*n+3:Nat):Int))=D1X := by
  rw [show 2*n+2=(2*n+1)+1 by omega,Val,
    if_neg (by intro h; cases h),if_neg (by omega),if_pos (by congr 2 <;> omega)]

theorem Val_even_top (n : Nat) :
    Val (2*n+2) (some ((2*n+4:Nat):Int))=X := by
  rw [show 2*n+2=(2*n+1)+1 by omega,Val]
  rw [if_neg (by intro h; cases h),if_neg (by omega)]
  rw [if_neg (by
    intro h
    injection h with h
    omega)]

theorem L_inj (a b : Nat) (h : L a=L b) : a=b := by
  have hl:=congrArg List.length h
  rw [length_L,length_L] at hl
  omega

theorem L_eq_L2 (a b : Nat) (h : L a=G2.L2 b) : a=0 ∧ b=1 := by
  have hl:=congrArg List.length h
  rw [length_L,G2.len_L2] at hl
  have hb:b=a+1:=by omega
  subst b
  cases a with
  | zero => exact ⟨rfl,rfl⟩
  | succ a =>
    have hd:=congrArg (fun q => q.getD 3 ((0:Int),(0:Int))) h
    simp [L,T,G2.L2,List.replicate_succ] at hd

theorem L_ne_base (k : Nat) : L k≠G1.Base := by
  intro h
  have hl:=congrArg List.length h
  rw [length_L] at hl
  simp [G1.Base] at hl

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  G2.Good2 p ∧ ∀ k req, p.1=(L k,req) → Allowed k req → p.2=Val k req

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p∈tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem good_L_entry (k : Nat) (req : Option Int) (hr : Allowed k req) :
    Good ((L k,req),Val k req) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      obtain ⟨hk,hj⟩:=L_eq_L2 k j (congrArg Prod.fst h)
      subst hk
      subst hj
      have hreq:req=none:=by simpa using congrArg Prod.snd h
      subst hreq
      rfl
    · intro j h
      obtain ⟨hk,hj⟩:=L_eq_L2 k j (congrArg Prod.fst h)
      subst hk
      subst hj
      have hreq:req=some 0:=by simpa using congrArg Prod.snd h
      subst hreq
      rfl
    · intro h
      exact absurd (congrArg Prod.fst h) (L_ne_base k)
  · intro j r h _
    have hL:L k=L j:=congrArg Prod.fst h
    have hkj:=L_inj k j hL
    subst hkj
    have hreq:req=r:=by simpa using congrArg Prod.snd h
    subst hreq
    rfl

theorem good_L2_entry (k : Nat) (req : Option Int) :
    Good ((G2.L2 k,req),G2.L2BT k) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      have hL:G2.L2 k=G2.L2 j:=congrArg Prod.fst h
      have hkj:=G2.L2_inj k j hL
      subst hkj
      rfl
    · intro j h
      have hL:G2.L2 k=G2.L2 j:=congrArg Prod.fst h
      have hkj:=G2.L2_inj k j hL
      subst hkj
      rfl
    · intro h
      exact absurd (congrArg Prod.fst h) (G2.L2_ne_base k)
  · intro j r h _
    obtain ⟨hj,hk⟩:=L_eq_L2 j k (congrArg Prod.fst h).symm
    subst hj
    subst hk
    rfl

theorem good_base_entry :
    Good ((G1.Base,(none:Option Int)),Trans.Dict.BT.zero) := by
  constructor
  · exact (G2.Sound2_cons_base [] G2.Sound2_nil) _ (by simp)
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (L_ne_base j)

theorem Sound_cons_L (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : Allowed k req) :
    Sound (((L k,req),Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    exact good_L_entry k req hr
  · exact hs p h

theorem Sound_cons_L2 (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) : Sound (((G2.L2 k,req),G2.L2BT k)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    exact good_L2_entry k req
  · exact hs p h

theorem Sound_cons_base (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    Sound (((G1.Base,(none:Option Int)),Trans.Dict.BT.zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    exact good_base_entry
  · exact hs p h

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun q=>q.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h),?_⟩
  have hb:p.1==key:=List.find?_some (p:=fun q=>q.1==key) (a:=p) h
  exact eq_of_beq hb

theorem value_L_of_good {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (hg : Good p) (k : Nat) (req : Option Int) (hr : Allowed k req)
    (he : p.1=(L k,req)) : p.2=Val k req :=
  hg.2 k req he hr

theorem run_base_ok (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).1=Trans.Dict.BT.zero ∧
      Sound ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(G1.Base,(none:Option Int))) with
  | some p =>
    rw [G1.run_hit f G1.Base none tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨hg.1.2.2 he,hs⟩
  | none =>
    rw [G1.run_base f tbl hf]
    exact ⟨rfl,Sound_cons_base tbl hs⟩

theorem runAux_L20 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 0) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) (G2.L2 0) req).run tbl).1=G2.L2BT 0 ∧
      Sound ((Trans.Recal.runAux (g+2) (G2.L2 0) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(G2.L2 0,req)) with
  | some p =>
    rw [show g+2=(g+1)+1 by omega,G1.run_hit (g+1) (G2.L2 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h
      exact hg.1.1 0 he
    · subst h
      exact hg.1.2.1 0 he
  | none =>
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,G2.isReducedP_L2 0,G2.isPrincipalP_L2 0,
      Bool.not_true,Bool.false_eq_true,if_false,G2.lenI_L2 0,
      show (((0:Nat):Int)+2-1==0)=false from by decide,
      show Trans.Recal.predP (G2.L2 0)=G1.Base from rfl]
    cases hrun:(Trans.Recal.runAux (g+1) G1.Base none) tbl with
    | mk a s =>
      have ih:=run_base_ok g tbl hs
      rw [show (Trans.Recal.runAux (g+1) G1.Base none).run tbl=(a,s) from hrun] at ih
      have ha:a=Trans.Dict.BT.zero:=ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,
        if_true]
      rcases hr with h|h
      · subst h
        exact ⟨rfl,Sound_cons_L2 s hsm 0 none⟩
      · subst h
        exact ⟨rfl,Sound_cons_L2 s hsm 0 (some 0)⟩

set_option maxHeartbeats 1000000 in
theorem runAux_L21 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 0) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+3) (G2.L2 1) req).run tbl).1=G2.L2BT 1 ∧
      Sound ((Trans.Recal.runAux (g+3) (G2.L2 1) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(G2.L2 1,req)) with
  | some p =>
    rw [show g+3=(g+2)+1 by omega,G1.run_hit (g+2) (G2.L2 1) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h
      exact hg.1.1 1 he
    · subst h
      exact hg.1.2.1 1 he
  | none =>
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,G2.isReducedP_L2 1,G2.isPrincipalP_L2 1,
      Bool.not_true,Bool.false_eq_true,if_false,G2.lenI_L2 1,
      show ((((1:Nat):Int)+2-1)==0)=false from by decide,
      show Trans.Recal.predP (G2.L2 1)=G2.L2 0 from G2.predP_L2 0]
    cases hrun:(Trans.Recal.runAux (g+2) (G2.L2 0) none) tbl with
    | mk a s =>
      have ih1:=runAux_L20 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) none).run tbl=(a,s) from hrun]
        at ih1
      have ha:a=G2.L2BT 0:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hrun,
        show ((G2.L2BT 0)==Trans.Dict.BT.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (G2.L2 1) 0 (((1:Nat):Int)+2-1) 0=1 from by rfl,
        show Trans.Recal.adm (G2.L2 1) 1=0 from G2.adm_L2_1 1 (by omega)]
      cases hrun2:(Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)) s with
      | mk c1 s2 =>
        have ih2:=runAux_L20 g (some 0) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=G2.L2BT 0:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun2,
          show Trans.Recal.mkC2 (G2.L2 1) 1 (((1:Nat):Int)+2-1)
            (Trans.Recal.transTypeMain (G2.L2 1) 1 (((1:Nat):Int)+2-1))
            (G2.L2BT 0)=G2.L2BT 1 from rfl]
        rcases hr with h|h
        · subst h
          rw [G2.replMark_L2BT
            ((G2.L2BT 0).size+((G2.L2BT 0).size+(G2.L2BT 1).size+4))
            0 (G2.L2BT 1) (by omega)]
          exact ⟨rfl,Sound_cons_L2 s2 hsm2 1 none⟩
        · subst h
          simp only [show ((0:Int)<((1:Nat):Int)+2-1) from by omega,if_true,
            StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          cases hrun3:(Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)) s2 with
          | mk c0 s3 =>
            have ih3:=runAux_L20 g (some 0) (Or.inr rfl) s2 hsm2
            rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0:c0=G2.L2BT 0:=ih3.1
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (G1.isMarkedB_self (G2.L2BT 0)),
              G2.replMark_L2BT
                ((G2.L2BT 0).size+((G2.L2BT 0).size+(G2.L2BT 1).size+4))
                0 (G2.L2BT 1) (by omega)]
            exact ⟨rfl,Sound_cons_L2 s3 hsm3 1 (some 0)⟩

theorem runAux_L0 (g : Nat) (req : Option Int) (hr : Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).2 := by
  have hr':req=none ∨ req=some 0:=hr
  simpa only [show L 0=G2.L2 1 from rfl,
    show Val 0 req=G2.L2BT 1 from rfl] using runAux_L21 g req hr' tbl hs

theorem size_W (k : Nat) (b : Trans.Dict.BT) :
    (W k b).size=4*k+b.size := by
  induction k with
  | zero => simp [W]
  | succ k ih =>
    simp only [W,Trans.Dict.BT.size,ih]
    omega

theorem size_LBT_odd (n : Nat) : (LBT (2*n+1)).size=4*n+10 := by
  rw [LBT_odd,Trans.Dict.BT.size,size_W,Trans.Dict.BT.size]
  omega

theorem size_LBT_even (n : Nat) : (LBT (2*n+2)).size=4*n+11 := by
  rw [LBT_even,Trans.Dict.BT.size,size_W,Trans.Dict.BT.size,Trans.Dict.BT.size]
  omega

theorem gp1_L_one_top : Trans.Recal.gp1 (L 1) 3=1 := rfl

set_option maxHeartbeats 1000000 in
theorem runAux_L1 (g : Nat) (req : Option Int) (hr : Allowed 1 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+4) (L 1) req).run tbl).1=Val 1 req ∧
      Sound ((Trans.Recal.runAux (g+4) (L 1) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(L 1,req)) with
  | some p =>
    rw [show g+4=(g+3)+1 by omega,G1.run_hit (g+3) (L 1) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg 1 req hr he,hs⟩
  | none =>
    rw [show g+4=(g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L 1,isPrincipalP_L 1,
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L 1,
      show (((1:Int)+3-1)==0)=false from by decide,
      show Trans.Recal.predP (L 1)=L 0 from predP_L 0]
    cases hrun:(Trans.Recal.runAux (g+3) (L 0) none) tbl with
    | mk a s =>
      have ih1:=runAux_L0 g none (Allowed_none 0) tbl hs
      rw [show (Trans.Recal.runAux (g+3) (L 0) none).run tbl=(a,s) from hrun]
        at ih1
      have ha:a=LBT 0:=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      cases hrun2:(Trans.Recal.runAux (g+3) (L 0) (some 0)) s with
      | mk c1 s2 =>
        have ih2:=runAux_L0 g (some 0) Allowed_zero_mark s hsm
        rw [show (Trans.Recal.runAux (g+3) (L 0) (some 0)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=LBT 0:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((1:Nat):Int)+3-1)=3 by omega,
          show ((3:Int)==0)=false from rfl,StateT.run,bind,StateT.bind,
          StateT.get,StateT.pure,pure,modify,modifyGet,MonadStateOf.modifyGet,
          StateT.modifyGet,get,getThe,MonadStateOf.get,Id.run,hrun,
          show ((LBT 0)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (L 1) 0 3 0=1 from by rfl,adm_L_one,hrun2,
          transType_L_one,mkC2_L_one]
        rcases hr with h|h
        · subst h
          rw [show LBT 0=.D 0 X from rfl,
            G1.replMark_self
              ((Trans.Dict.BT.D 0 X).size+((Trans.Dict.BT.D 0 X).size+
                (LBT 1).size+4)) 0 X (LBT 1) (by omega)]
          refine ⟨Val_none 1,?_⟩
          have ht:=Sound_cons_L s2 hsm2 1 none (Allowed_none 1)
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬((3:Int)<(1:Int)+3-1) by omega,if_false,
            gp1_L_one_top,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          refine ⟨(Val_odd_top 0).symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 1 (some 3) (Allowed_odd_top 0)
          rw [show Val 1 (some 3)=D1z from Val_odd_top 0] at ht
          exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_even_step (n g : Nat) (req : Option Int)
    (hr : Allowed (2*n+2) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (2*n+1) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1)) r).run s).1=
            Val (2*n+1) r ∧
          Sound ((Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1)) r).run s).2) :
    ((Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2)) req).run tbl).1=
        Val (2*n+2) req ∧
      Sound ((Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((2*n+3:Nat):Int) ∨
      req=some ((2*n+4:Nat):Int) := by
    rw [show 2*n+2=(2*n+1)+1 by omega,Allowed,if_neg (by omega)] at hr
    simpa only [
      show 2*n+1+2=2*n+3 by omega,show 2*n+1+3=2*n+4 by omega] using hr
  cases hf:tbl.find? (fun q=>q.1==(L (2*n+2),req)) with
  | some p =>
    rw [show (2*n+2)+g+3=((2*n+1)+g+3)+1 by omega,
      G1.run_hit ((2*n+1)+g+3) (L (2*n+2)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (2*n+2) req hr he,hs⟩
  | none =>
    rw [show (2*n+2)+g+3=((2*n+1)+g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (2*n+2),isPrincipalP_L (2*n+2),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (2*n+2),
      show ((((2*n+2:Nat):Int)+3-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (2*n+2))=L (2*n+1) from by
        simpa only [show 2*n+2=(2*n+1)+1 by omega] using predP_L (2*n+1)]
    cases hrun:(Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1)) none) tbl with
    | mk a s =>
      have ih1:=ih none (Allowed_none (2*n+1)) tbl hs
      rw [show (Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1)) none).run tbl=
        (a,s) from hrun] at ih1
      have ha:a=LBT (2*n+1):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [show (((2*n+2:Nat):Int)+3-1)=((2*n+4:Nat):Int) by omega,
        StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hrun,
        show ((LBT (2*n+1))==Trans.Dict.BT.zero)=false from by
          rw [LBT_odd]; rfl,
        Bool.false_eq_true,if_false,fpar_L_even_top,
        adm_L_row1 (2*n+2) n (by omega)]
      cases hrun2:(Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1))
          (some ((2*n+3:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((2*n+3:Nat):Int)) (Allowed_odd_top n) s hsm
        rw [show (Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1))
          (some ((2*n+3:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1z:=ih2.1.trans (Val_odd_top n)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun2,transType_L_even,mkC2_L_even]
        rcases hr' with h|h|h
        · subst h
          rw [repl_LBT_odd
            ((LBT (2*n+1)).size+(D1z.size+D1X.size+4)) n (by
              rw [size_LBT_odd]
              omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (2*n+2),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (2*n+2) none (Allowed_none (2*n+2))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show (((2*n+3:Nat):Int)<((2*n+4:Nat):Int)) by omega,
            if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          cases hrun3:(Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1))
              (some ((2*n+3:Nat):Int))) s2 with
          | mk c0 s3 =>
            have ih3:=ih (some ((2*n+3:Nat):Int)) (Allowed_odd_top n) s2 hsm2
            rw [show (Trans.Recal.runAux ((2*n+1)+g+3) (L (2*n+1))
              (some ((2*n+3:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
            have hc0:c0=D1z:=ih3.1.trans (Val_odd_top n)
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (G1.isMarkedB_self D1z),
              G1.replMark_self (D1z.size+(D1z.size+D1X.size+4)) 1 .zero D1X
                (by omega)]
            refine ⟨(Val_even_own n).symm,?_⟩
            have ht:=Sound_cons_L s3 hsm3 (2*n+2)
              (some ((2*n+3:Nat):Int)) (Allowed_even_own n)
            rw [Val_even_own] at ht
            exact ht
        · subst h
          simp only [show ¬(((2*n+4:Nat):Int)<((2*n+4:Nat):Int)) by omega,
            if_false,gp1_L_even_top,StateT.run,bind,StateT.bind,StateT.get,
            StateT.pure,pure,modify,modifyGet,MonadStateOf.modifyGet,
            StateT.modifyGet,get,getThe,MonadStateOf.get,Id.run]
          refine ⟨(Val_even_top n).symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 (2*n+2)
            (some ((2*n+4:Nat):Int)) (Allowed_even_top n)
          rw [Val_even_top] at ht
          exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_odd_step (n g : Nat) (req : Option Int)
    (hr : Allowed (2*n+3) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (2*n+2) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2)) r).run s).1=
            Val (2*n+2) r ∧
          Sound ((Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2)) r).run s).2) :
    ((Trans.Recal.runAux ((2*n+3)+g+3) (L (2*n+3)) req).run tbl).1=
        Val (2*n+3) req ∧
      Sound ((Trans.Recal.runAux ((2*n+3)+g+3) (L (2*n+3)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((2*n+5:Nat):Int) := by
    rw [show 2*n+3=(2*n+2)+1 by omega,Allowed,if_pos (by omega)] at hr
    simpa only [show 2*n+2+3=2*n+5 by omega] using hr
  cases hf:tbl.find? (fun q=>q.1==(L (2*n+3),req)) with
  | some p =>
    rw [show (2*n+3)+g+3=((2*n+2)+g+3)+1 by omega,
      G1.run_hit ((2*n+2)+g+3) (L (2*n+3)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (2*n+3) req hr he,hs⟩
  | none =>
    rw [show (2*n+3)+g+3=((2*n+2)+g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (2*n+3),isPrincipalP_L (2*n+3),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (2*n+3),
      show ((((2*n+3:Nat):Int)+3-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (2*n+3))=L (2*n+2) from by
        simpa only [show 2*n+3=(2*n+2)+1 by omega] using predP_L (2*n+2)]
    cases hrun:(Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2)) none) tbl with
    | mk a s =>
      have ih1:=ih none (Allowed_none (2*n+2)) tbl hs
      rw [show (Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2)) none).run tbl=
        (a,s) from hrun] at ih1
      have ha:a=LBT (2*n+2):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [show (((2*n+3:Nat):Int)+3-1)=((2*n+5:Nat):Int) by omega,
        StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hrun,
        show ((LBT (2*n+2))==Trans.Dict.BT.zero)=false from by
          rw [LBT_even]; rfl,
        Bool.false_eq_true,if_false,fpar_L_odd_top,
        adm_L_row1 (2*n+3) n (by omega)]
      cases hrun2:(Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2))
          (some ((2*n+3:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((2*n+3:Nat):Int)) (Allowed_even_own n) s hsm
        rw [show (Trans.Recal.runAux ((2*n+2)+g+3) (L (2*n+2))
          (some ((2*n+3:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1X:=ih2.1.trans (Val_even_own n)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun2,transType_L_odd,mkC2_L_odd]
        rcases hr' with h|h
        · subst h
          have hsize : 2*n+6≤(LBT (2*n+2)).size+
              (D1X.size+(Trans.Dict.BT.D 1 (W 1 .zero)).size+4) := by
            rw [size_LBT_even]
            omega
          rw [repl_LBT_even _ n hsize]
          simp only [Option.getD_some]
          refine ⟨Val_none (2*n+3),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (2*n+3) none (Allowed_none (2*n+3))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬(((2*n+5:Nat):Int)<((2*n+5:Nat):Int)) by omega,
            if_false,gp1_L_odd_top,StateT.run,bind,StateT.bind,StateT.get,
            StateT.pure,pure,modify,modifyGet,MonadStateOf.modifyGet,
            StateT.modifyGet,get,getThe,MonadStateOf.get,Id.run]
          refine ⟨(Val_odd_top (n+1)).symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 (2*n+3)
            (some ((2*n+5:Nat):Int)) (by
              simpa only [show 2*(n+1)+1=2*n+3 by omega,
                show 2*(n+1)+3=2*n+5 by omega] using Allowed_odd_top (n+1))
          rw [show Val (2*n+3) (some ((2*n+5:Nat):Int))=D1z from by
            simpa only [show 2*(n+1)+1=2*n+3 by omega,
              show 2*(n+1)+3=2*n+5 by omega] using Val_odd_top (n+1)] at ht
          exact ht

def RunOK (k : Nat) : Prop :=
  ∀ g : Nat, ∀ req : Option Int, Allowed k req →
    ∀ tbl : Trans.Recal.Memo, Sound tbl →
      ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).1=Val k req ∧
        Sound ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).2

theorem runOK_zero : RunOK 0 := by
  intro g req hr tbl hs
  simpa only [Nat.zero_add] using runAux_L0 g req hr tbl hs

theorem runOK_one : RunOK 1 := by
  intro g req hr tbl hs
  simpa only [show 1+g+3=g+4 by omega] using runAux_L1 g req hr tbl hs

theorem runOK_even_step (n : Nat) (ih : RunOK (2*n+1)) :
    RunOK (2*n+2) := by
  intro g req hr tbl hs
  exact runAux_even_step n g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_odd_step (n : Nat) (ih : RunOK (2*n+2)) :
    RunOK (2*n+3) := by
  intro g req hr tbl hs
  exact runAux_odd_step n g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_pair (n : Nat) : RunOK (2*n+1) ∧ RunOK (2*n+2) := by
  induction n with
  | zero =>
    have ho : RunOK (2*0+1) := by simpa only using runOK_one
    exact ⟨ho,runOK_even_step 0 ho⟩
  | succ n ih =>
    have ho' := runOK_odd_step n ih.2
    have ho : RunOK (2*(n+1)+1) := by
      simpa only [show 2*(n+1)+1=2*n+3 by omega] using ho'
    exact ⟨ho,runOK_even_step (n+1) ho⟩

set_option maxHeartbeats 2000000 in
theorem runAux_L (k g : Nat) (req : Option Int) (hr : Allowed k req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).2 := by
  have hk : RunOK k := by
    cases k with
    | zero => exact runOK_zero
    | succ q =>
      rcases Nat.mod_two_eq_zero_or_one q with hq|hq
      · have hdiv:=Nat.mod_add_div q 2
        have heq : q+1=2*(q/2)+1 := by omega
        rw [heq]
        exact (runOK_pair (q/2)).1
      · have hdiv:=Nat.mod_add_div q 2
        have heq : q+1=2*(q/2)+2 := by omega
        rw [heq]
        exact (runOK_pair (q/2)).2
  exact hk g req hr tbl hs

/-- Link 2: the recalibrated reader follows the entire alternating ladder. -/
theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m)=LBT m := by
  have hb : m+3≤Trans.Recal.transFuel (L m) := by
    show m+3≤40+6*((L m).length+Trans.Recal.maxE (L m))
    rw [length_L]
    omega
  have h : Trans.Recal.transFuel (L m)=
      m+(Trans.Recal.transFuel (L m)-m-3)+3 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L m)) (L m) none).run []).1=_
  rw [h]
  simpa only [Val_none] using
    (runAux_L m _ none (Allowed_none m) [] Sound_nil).1

#guard (List.range 16).all fun m =>
  Trans.Recal.redP (L m)==L m && Trans.Recal.trMax (L m)==2

#guard (List.range 12).all fun m => Trans.Recal.transPort (L m)==LBT m

/-! ### Link 3 and composition. -/

theorem W_eq_G6Dict (k : Nat) (b : Trans.Dict.BT) :
    W k b=G6Dict.W k b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [W,G6Dict.W,ih]

theorem dict_LBT_even (n : Nat) :
    Trans.Dict.dict (LBT (2*n+2))=fF (n+1) := by
  rw [LBT_even,W_eq_G6Dict]
  exact G6Dict.dict_D0_W_fF n

theorem one_plus_fF (n : Nat) : plus TM.Term.one (fF n)=fF n := by
  cases n <;> rfl

theorem one_plus_dict_LBT_even (n : Nat) :
    plus TM.Term.one (Trans.Dict.dict (LBT (2*n)))=fF n := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [show 2*(n+1)=2*n+2 by omega,dict_LBT_even,one_plus_fF]

/-- The selected `ψ₀(φ̄(1,Ω)+φ̄(1,Ω))` row has its closed expansion
    sequence for every `n`. -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fF n) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map Trans.Recal.transPort).map
          (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=_
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    cases n <;> rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_L,one_plus_dict_LBT_even]

#guard (List.range 8).all fun n => Trans.oR (BMS.expand M n)==some (fF n)
#print axioms oR_M



end G6
end Rows.Selected
