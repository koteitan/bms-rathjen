import Rows.G9

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G10

def M : BMS.Matrix := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1]]
def t : Term := phi (add (phi zero zero) (phi zero zero))
  (phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
    (phi zero (phi zero zero)))

/-- Row-zero value of the `0,1,1,1,0,1` six-column tail. -/
def p (k : Nat) : Int :=
  if k%6=0 then ((2*(k/6)+2:Nat):Int)
  else if k%6=1 ∨ k%6=5 then ((2*(k/6)+3:Nat):Int)
  else ((2*(k/6)+4:Nat):Int)

/-- Row-one value of the six-column tail. -/
def q (k : Nat) : Int := if k%6=0 ∨ k%6=4 then 0 else 1

def T (m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k => (p k,q k)

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS :=
  [(0,0),(1,1),(2,1),(2,1),(2,0),(1,1)]++T m

abbrev D0z : Trans.Dict.BT := .D 0 .zero
abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev D11z : Trans.Dict.BT := .D 1 D1z
abbrev D1ss : Trans.Dict.BT := .D 1 (.sum D1z D1z)
abbrev C : Trans.Dict.BT := .sum D1z (.sum D1z D0z)
abbrev A0 : Trans.Dict.BT := .D 1 C
abbrev Anchor : Trans.Dict.BT := .D 0 A0
abbrev B0 : Trans.Dict.BT := .sum A0 D1z

/-- A complete block wraps the unfinished suffix in the reader output. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0,b => b
  | n+1,b => .sum A0 (.D 1 (.D 0 (W n b)))

def Part : Nat → Trans.Dict.BT
  | 0 => B0
  | 1 => .sum A0 (.D 1 D0z)
  | 2 => .sum A0 (.D 1 (.D 0 D1z))
  | 3 => .sum A0 (.D 1 (.D 0 D11z))
  | 4 => .sum A0 (.D 1 (.D 0 D1ss))
  | _ => .sum A0 (.D 1 (.D 0 A0))

/-- Reader output on every one-column prefix of the six-phase ladder. -/
def LBT (m : Nat) : Trans.Dict.BT := .D 0 (W (m/6) (Part (m%6)))

theorem T_succ (m : Nat) : T (m+1)=T m++[(p m,q m)] := by
  unfold T
  rw [List.range_succ,List.map_append]
  rfl

theorem L_succ (m : Nat) : L (m+1)=L m++[(p m,q m)] := by
  unfold L
  rw [T_succ,List.append_assoc]

theorem length_T (m : Nat) : (T m).length=m := by simp [T]

theorem length_L (m : Nat) : (L m).length=m+6 := by simp [L,length_T]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+6 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1))=L m := by
  rw [L_succ]
  unfold Trans.Recal.predP
  rw [show ((L m++[(p m,q m)]).length==1)=false from by
    rw [List.length_append,length_L]
    simp]
  simp

/-! ### Link 1: expansion and parsing. -/

theorem expand_block_first : (fun a : Nat =>
      ([[0+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1],
        [2+a*2*1,1+a*0*1],[2+a*2*1,1+a*0*1],
        [2+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1]] : BMS.Matrix))=
      fun a => [[2*a,0],[1+2*a,1],[2+2*a,1],[2+2*a,1],[2+2*a,0],
        [1+2*a,1]] := by
  funext a
  simp [Nat.mul_comm]

theorem expand_block_succ : ((fun a : Nat =>
      ([[2*a,0],[1+2*a,1],[2+2*a,1],[2+2*a,1],[2+2*a,0],
        [1+2*a,1]]:BMS.Matrix)) ∘ Nat.succ)=
      fun a => [[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
        [3+2*a,1]] := by
  funext a
  simp only [Function.comp_apply]
  rw [show 2*(a+1)=2+2*a by omega,
    show 1+(2+2*a)=3+2*a by omega,
    show 2+(2+2*a)=4+2*a by omega]

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]++
      ((List.range n).map fun a =>
        ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
          [3+2*a,1]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 0++
      ((List.range (n+1)).map fun a =>
        ([[0+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1],
          [2+a*2*1,1+a*0*1],[2+a*2*1,1+a*0*1],
          [2+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1]] : BMS.Matrix)).flatten) := rfl
  rw [h,expand_block_first,List.range_succ_eq_map]
  simp only [Option.getD_some,M,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.singleton_append,List.nil_append]
  rw [expand_block_succ]

theorem p_phase0 (a : Nat) : p (6*a)=((2*a+2:Nat):Int) := by simp [p]
theorem p_phase1 (a : Nat) : p (6*a+1)=((2*a+3:Nat):Int) := by simp [p]; omega
theorem p_phase2 (a : Nat) : p (6*a+2)=((2*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase3 (a : Nat) : p (6*a+3)=((2*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase4 (a : Nat) : p (6*a+4)=((2*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase5 (a : Nat) : p (6*a+5)=((2*a+3:Nat):Int) := by simp [p]; omega
theorem q_phase0 (a : Nat) : q (6*a)=0 := by simp [q]
theorem q_phase1 (a : Nat) : q (6*a+1)=1 := by simp [q]
theorem q_phase2 (a : Nat) : q (6*a+2)=1 := by simp [q]
theorem q_phase3 (a : Nat) : q (6*a+3)=1 := by simp [q]
theorem q_phase4 (a : Nat) : q (6*a+4)=0 := by simp [q]
theorem q_phase5 (a : Nat) : q (6*a+5)=1 := by simp [q]

theorem T_six_mul (n : Nat) :
    T (6*n)=((List.range n).map fun a =>
      ([(((2*a+2:Nat):Int),(0:Int)),(((2*a+3:Nat):Int),(1:Int)),
        (((2*a+4:Nat):Int),(1:Int)),(((2*a+4:Nat):Int),(1:Int)),
        (((2*a+4:Nat):Int),(0:Int)),(((2*a+3:Nat):Int),(1:Int))]
        : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1)=6*n+6 by omega,T_succ,T_succ,T_succ,T_succ,T_succ,T_succ,ih,
      List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc,
      List.singleton_append]
    rw [show 6*n+1=6*n+1 by rfl,show 6*n+2=6*n+2 by rfl,
      show 6*n+3=6*n+3 by rfl,show 6*n+4=6*n+4 by rfl,
      show 6*n+5=6*n+5 by rfl,
      p_phase0 n,q_phase0 n,p_phase1 n,q_phase1 n,p_phase2 n,q_phase2 n,
      p_phase3 n,q_phase3 n,p_phase4 n,q_phase4 n,p_phase5 n,q_phase5 n]
    simp only [List.cons_append,List.nil_append]

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
        [3+2*a,1]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=T (6*n) := by
  rw [T_six_mul,List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  change [(((2+2*a:Nat):Int),0),(((3+2*a:Nat):Int),1),
    (((4+2*a:Nat):Int),1),(((4+2*a:Nat):Int),1),
    (((4+2*a:Nat):Int),0),(((3+2*a:Nat):Int),1)]=_
  rw [show 2+2*a=2*a+2 by omega,show 3+2*a=2*a+3 by omega,
    show 4+2*a=2*a+4 by omega]

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
        [3+2*a,1]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by simp

/-- Link 1: each expansion lands on a six-column-complete prefix. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (6*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]:BMS.Matrix)++
      ((List.range n).map fun a =>
        ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
          [3+2*a,1]]:BMS.Matrix)).flatten).isEmpty=false
      from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (6*n))
#guard (List.range 18).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard rest12.any fun r => r.m==M && r.t==t

/-! ### Row-zero parent structure. -/

theorem getD_T (m k : Nat) (hk : k<m) :
    (T m).getD k (0,0)=(p k,q k) := by
  unfold T
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem gp0_T (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (T m) (k:Int)=p k := by
  show (if (k:Int)<0 then 0 else ((T m).getD k (0,0)).1)=_
  rw [if_neg (by omega),getD_T m k hk]

theorem gp1_T (m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (T m) (k:Int)=q k := by
  show (if (k:Int)<0 then 0 else ((T m).getD k (0,0)).2)=_
  rw [if_neg (by omega),getD_T m k hk]

theorem gp0_L (m k : Nat) (hk : k<m+6) :
    Trans.Recal.gp0 (L m) (k:Int)=
      if k<6 then ([0,1,2,2,2,1].getD k 0:Int) else p (k-6) := by
  by_cases h6:k<6
  · simp only [if_pos h6]
    have hc:k=0∨k=1∨k=2∨k=3∨k=4∨k=5:=by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp only [if_neg h6]
    obtain ⟨j,rfl⟩ : ∃ j,k=j+6 := ⟨k-6,by omega⟩
    show (if (((j+6:Nat):Int)<0) then 0 else ((L m).getD (j+6) (0,0)).1)=p j
    rw [if_neg (by omega)]
    change ((T m).getD j (0,0)).1=p j
    rw [getD_T m j (by omega)]

theorem gp1_L (m k : Nat) (hk : k<m+6) :
    Trans.Recal.gp1 (L m) (k:Int)=
      if k<6 then ([0,1,1,1,0,1].getD k 0:Int) else q (k-6) := by
  by_cases h6:k<6
  · simp only [if_pos h6]
    have hc:k=0∨k=1∨k=2∨k=3∨k=4∨k=5:=by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp only [if_neg h6]
    obtain ⟨j,rfl⟩ : ∃ j,k=j+6 := ⟨k-6,by omega⟩
    show (if (((j+6:Nat):Int)<0) then 0 else ((L m).getD (j+6) (0,0)).2)=q j
    rw [if_neg (by omega)]
    change ((T m).getD j (0,0)).2=q j
    rw [getD_T m j (by omega)]

theorem fpar_L_base_one (m : Nat) : Trans.Recal.fpar (L m) 0 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_base_two (m : Nat) : Trans.Recal.fpar (L m) 0 2 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_base_three (m : Nat) : Trans.Recal.fpar (L m) 0 3 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_base_four (m : Nat) : Trans.Recal.fpar (L m) 0 4 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_base_five (m : Nat) : Trans.Recal.fpar (L m) 0 5 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem gp0_L_phase0 (a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp0 (L m) ((6*a+6:Nat):Int)=((2*a+2:Nat):Int) := by
  rw [gp0_L m (6*a+6) (by omega),if_neg (by omega)]
  simpa only [show 6*a+6-6=6*a by omega] using p_phase0 a

theorem gp0_L_phase1 (a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.gp0 (L m) ((6*a+7:Nat):Int)=((2*a+3:Nat):Int) := by
  rw [gp0_L m (6*a+7) (by omega),if_neg (by omega)]
  simpa only [show 6*a+7-6=6*a+1 by omega] using p_phase1 a

theorem gp0_L_phase2 (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.gp0 (L m) ((6*a+8:Nat):Int)=((2*a+4:Nat):Int) := by
  rw [gp0_L m (6*a+8) (by omega),if_neg (by omega)]
  simpa only [show 6*a+8-6=6*a+2 by omega] using p_phase2 a

theorem gp0_L_phase3 (a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.gp0 (L m) ((6*a+9:Nat):Int)=((2*a+4:Nat):Int) := by
  rw [gp0_L m (6*a+9) (by omega),if_neg (by omega)]
  simpa only [show 6*a+9-6=6*a+3 by omega] using p_phase3 a

theorem gp0_L_phase4 (a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.gp0 (L m) ((6*a+10:Nat):Int)=((2*a+4:Nat):Int) := by
  rw [gp0_L m (6*a+10) (by omega),if_neg (by omega)]
  simpa only [show 6*a+10-6=6*a+4 by omega] using p_phase4 a

theorem gp0_L_phase5 (a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.gp0 (L m) ((6*a+11:Nat):Int)=((2*a+3:Nat):Int) := by
  rw [gp0_L m (6*a+11) (by omega),if_neg (by omega)]
  simpa only [show 6*a+11-6=6*a+5 by omega] using p_phase5 a

theorem gp0_L_before_phase0 (a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp0 (L m) ((6*a+5:Nat):Int)=((2*a+1:Nat):Int) := by
  cases a with
  | zero => rfl
  | succ a =>
    simpa only [show 6*(a+1)+5=6*a+11 by omega,
      show 2*(a+1)+1=2*a+3 by omega] using gp0_L_phase5 a m (by omega)

theorem fpar_L_phase0 (a m : Nat) (h : 6*a<m) :
    Trans.Recal.fpar (L m) 0 ((6*a+6:Nat):Int) 0=(6*a+5:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((6*a+6:Nat):Int)-1=((6*a+5:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+7) (L m)
    (Trans.Recal.gp0 (L m) ((6*a+6:Nat):Int)) ((6*a+5:Nat):Int) 0=_
  rw [gp0_L_phase0 a m h,show m+7=(m+6)+1 by omega,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_L_before_phase0 a m h,
    if_pos (by omega)]

theorem fpar_L_phase1 (a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.fpar (L m) 0 ((6*a+7:Nat):Int) 0=(6*a+6:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((6*a+7:Nat):Int)-1=((6*a+6:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+7) (L m)
    (Trans.Recal.gp0 (L m) ((6*a+7:Nat):Int)) ((6*a+6:Nat):Int) 0=_
  rw [gp0_L_phase1 a m h,show m+7=(m+6)+1 by omega,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_L_phase0 a m (by omega),
    if_pos (by omega)]

theorem fpar_L_phase2 (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.fpar (L m) 0 ((6*a+8:Nat):Int) 0=(6*a+7:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((6*a+8:Nat):Int)-1=((6*a+7:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+7) (L m)
    (Trans.Recal.gp0 (L m) ((6*a+8:Nat):Int)) ((6*a+7:Nat):Int) 0=_
  rw [gp0_L_phase2 a m h,show m+7=(m+6)+1 by omega,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_L_phase1 a m (by omega),
    if_pos (by omega)]

theorem fpar_L_phase3 (a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.fpar (L m) 0 ((6*a+9:Nat):Int) 0=(6*a+7:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((6*a+9:Nat):Int)-1=((6*a+8:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+7) (L m)
    (Trans.Recal.gp0 (L m) ((6*a+9:Nat):Int)) ((6*a+8:Nat):Int) 0=_
  rw [gp0_L_phase3 a m h,show m+7=(m+6)+1 by omega,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_L_phase2 a m (by omega),
    if_neg (by omega),show ((6*a+8:Nat):Int)-1=((6*a+7:Nat):Int) by omega,
    show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_L_phase1 a m (by omega),if_pos (by omega)]

theorem fpar_L_phase4 (a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.fpar (L m) 0 ((6*a+10:Nat):Int) 0=(6*a+7:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((6*a+10:Nat):Int)-1=((6*a+9:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+7) (L m)
    (Trans.Recal.gp0 (L m) ((6*a+10:Nat):Int)) ((6*a+9:Nat):Int) 0=_
  rw [gp0_L_phase4 a m h,show m+7=(m+6)+1 by omega,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_L_phase3 a m (by omega),
    if_neg (by omega),show ((6*a+9:Nat):Int)-1=((6*a+8:Nat):Int) by omega,
    show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_L_phase2 a m (by omega),if_neg (by omega),
    show ((6*a+8:Nat):Int)-1=((6*a+7:Nat):Int) by omega,
    show m+5=(m+4)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_L_phase1 a m (by omega),if_pos (by omega)]

theorem fpar_L_phase5 (a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.fpar (L m) 0 ((6*a+11:Nat):Int) 0=(6*a+6:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((6*a+11:Nat):Int)-1=((6*a+10:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+7) (L m)
    (Trans.Recal.gp0 (L m) ((6*a+11:Nat):Int)) ((6*a+10:Nat):Int) 0=_
  rw [gp0_L_phase5 a m h,show m+7=(m+6)+1 by omega,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_L_phase4 a m (by omega),
    if_neg (by omega),show ((6*a+10:Nat):Int)-1=((6*a+9:Nat):Int) by omega,
    show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_L_phase3 a m (by omega),if_neg (by omega),
    show ((6*a+9:Nat):Int)-1=((6*a+8:Nat):Int) by omega,
    show m+5=(m+4)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_L_phase2 a m (by omega),if_neg (by omega),
    show ((6*a+8:Nat):Int)-1=((6*a+7:Nat):Int) by omega,
    show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_L_phase1 a m (by omega),if_neg (by omega),
    show ((6*a+7:Nat):Int)-1=((6*a+6:Nat):Int) by omega,
    show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_L_phase0 a m (by omega),if_pos (by omega)]

def parentL (k : Nat) : Nat :=
  if k=0 then 0 else if k=1 then 0 else if k<5 then 1 else if k=5 then 0
  else
    let j:=k-6
    if j%6=0 ∨ j%6=1 ∨ j%6=2 then k-1
    else if j%6=3 then k-2 else if j%6=4 then k-3 else k-5

theorem parentL_lt (k : Nat) (hk : 0<k) : parentL k<k := by
  unfold parentL
  split <;> rename_i h0
  · omega
  split <;> rename_i h1
  · omega
  split <;> rename_i h5
  · omega
  split <;> rename_i h5e
  · omega
  dsimp only
  split <;> rename_i hp012
  · omega
  split <;> rename_i hp3
  · omega
  split <;> omega

theorem parentL_phase0 (a : Nat) : parentL (6*a+6)=6*a+5 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_pos (by left; omega)]
  omega
theorem parentL_phase1 (a : Nat) : parentL (6*a+7)=6*a+6 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_pos (by right; left; omega)]
  omega
theorem parentL_phase2 (a : Nat) : parentL (6*a+8)=6*a+7 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_pos (by right; right; omega)]
  omega
theorem parentL_phase3 (a : Nat) : parentL (6*a+9)=6*a+7 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega),if_pos (by omega)]
  omega
theorem parentL_phase4 (a : Nat) : parentL (6*a+10)=6*a+7 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  omega
theorem parentL_phase5 (a : Nat) : parentL (6*a+11)=6*a+6 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  omega

theorem fpar_L_parent (m k : Nat) (hk0 : 0<k) (hk : k<m+6) :
    Trans.Recal.fpar (L m) 0 (k:Int) 0=(parentL k:Nat) := by
  by_cases h6:k<6
  · have hc:k=0∨k=1∨k=2∨k=3∨k=4∨k=5:=by omega
    rcases hc with h0|h1|h2|h3|h4|h5
    · omega
    · subst k
      change Trans.Recal.fpar (L m) 0 1 0=0
      exact fpar_L_base_one m
    · subst k
      change Trans.Recal.fpar (L m) 0 2 0=1
      exact fpar_L_base_two m
    · subst k
      change Trans.Recal.fpar (L m) 0 3 0=1
      exact fpar_L_base_three m
    · subst k
      change Trans.Recal.fpar (L m) 0 4 0=1
      exact fpar_L_base_four m
    · subst k
      change Trans.Recal.fpar (L m) 0 5 0=0
      exact fpar_L_base_five m
  · obtain ⟨j,rfl⟩ : ∃ j,k=j+6 := ⟨k-6,by omega⟩
    have hj : j<m := by omega
    have hm : j%6=0 ∨ j%6=1 ∨ j%6=2 ∨ j%6=3 ∨ j%6=4 ∨ j%6=5 := by omega
    rcases hm with h0|h1|h2|h3|h4|h5
    · have heq:j=6*(j/6):=by omega
      rw [heq,show 6*(j/6)+6=6*(j/6)+6 by rfl,parentL_phase0]
      exact fpar_L_phase0 (j/6) m (by omega)
    · have heq:j=6*(j/6)+1:=by omega
      rw [heq]
      rw [show 6*(j/6)+1+6=6*(j/6)+7 by omega]
      rw [parentL_phase1]
      exact fpar_L_phase1 (j/6) m (by omega)
    · have heq:j=6*(j/6)+2:=by omega
      rw [heq]
      rw [show 6*(j/6)+2+6=6*(j/6)+8 by omega]
      rw [parentL_phase2]
      exact fpar_L_phase2 (j/6) m (by omega)
    · have heq:j=6*(j/6)+3:=by omega
      rw [heq]
      rw [show 6*(j/6)+3+6=6*(j/6)+9 by omega]
      rw [parentL_phase3]
      exact fpar_L_phase3 (j/6) m (by omega)
    · have heq:j=6*(j/6)+4:=by omega
      rw [heq]
      rw [show 6*(j/6)+4+6=6*(j/6)+10 by omega]
      rw [parentL_phase4]
      exact fpar_L_phase4 (j/6) m (by omega)
    · have heq:j=6*(j/6)+5:=by omega
      rw [heq]
      rw [show 6*(j/6)+5+6=6*(j/6)+11 by omega]
      rw [parentL_phase5]
      exact fpar_L_phase5 (j/6) m (by omega)

theorem isAncAux_L (m k : Nat) : ∀ f : Nat, k<m+6 → k<f →
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k=>∀ f:Nat,k<m+6→k<f→
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_L_parent m k (by omega) hkm]
      rw [show (((parentL k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hp:=parentL_lt k (by omega)
      exact ih (parentL k) hp f (by omega) (by omega)

theorem isAnc_L (m k : Nat) (hk : k<m+6) :
    Trans.Recal.isAnc (L m) 0 (k:Int) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  exact isAncAux_L m k (m+7) hk (by omega)

theorem isPrincipalP_L (m : Nat) : Trans.Recal.isPrincipalP (L m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (L m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_L]
    simp]
  simp only [Bool.not_false,Bool.true_and]
  rw [show Trans.Recal.lenI (L m)-1=((m+5:Nat):Int) from by rw [lenI_L]; omega]
  exact isAnc_L m (m+5) (by omega)

/-! ### Principal decomposition of the periodic tail. -/

theorem lenI_T (m : Nat) : Trans.Recal.lenI (T m)=(m:Int) := by
  unfold Trans.Recal.lenI
  rw [length_T]

theorem gp0_T_phase0 (a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp0 (T m) ((6*a:Nat):Int)=((2*a+2:Nat):Int) := by
  simpa only [p_phase0 a] using gp0_T m (6*a) h

theorem gp0_T_phase1 (a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.gp0 (T m) ((6*a+1:Nat):Int)=((2*a+3:Nat):Int) := by
  simpa only [p_phase1 a] using gp0_T m (6*a+1) h

theorem gp0_T_phase2 (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.gp0 (T m) ((6*a+2:Nat):Int)=((2*a+4:Nat):Int) := by
  simpa only [p_phase2 a] using gp0_T m (6*a+2) h

theorem gp0_T_phase3 (a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.gp0 (T m) ((6*a+3:Nat):Int)=((2*a+4:Nat):Int) := by
  simpa only [p_phase3 a] using gp0_T m (6*a+3) h

theorem gp0_T_phase4 (a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.gp0 (T m) ((6*a+4:Nat):Int)=((2*a+4:Nat):Int) := by
  simpa only [p_phase4 a] using gp0_T m (6*a+4) h

theorem gp0_T_phase5 (a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.gp0 (T m) ((6*a+5:Nat):Int)=((2*a+3:Nat):Int) := by
  simpa only [p_phase5 a] using gp0_T m (6*a+5) h

theorem fpar_T_phase0 (a m : Nat) (h : 6*(a+1)<m) :
    Trans.Recal.fpar (T m) 0 ((6*(a+1):Nat):Int) 0=(6*a+5:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((6*(a+1):Nat):Int)-1=((6*a+5:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((6*(a+1):Nat):Int)) ((6*a+5:Nat):Int) 0=_
  rw [gp0_T_phase0 (a+1) m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase5 a m (by omega),if_pos (by omega)]

theorem fpar_T_phase1 (a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.fpar (T m) 0 ((6*a+1:Nat):Int) 0=(6*a:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((6*a+1:Nat):Int)-1=((6*a:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((6*a+1:Nat):Int)) ((6*a:Nat):Int) 0=_
  rw [gp0_T_phase1 a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase0 a m (by omega),if_pos (by omega)]

theorem fpar_T_phase2 (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.fpar (T m) 0 ((6*a+2:Nat):Int) 0=(6*a+1:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((6*a+2:Nat):Int)) ((6*a+1:Nat):Int) 0=_
  rw [gp0_T_phase2 a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase1 a m (by omega),if_pos (by omega)]

theorem fpar_T_phase3 (a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.fpar (T m) 0 ((6*a+3:Nat):Int) 0=(6*a+1:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((6*a+3:Nat):Int)) ((6*a+2:Nat):Int) 0=_
  rw [gp0_T_phase3 a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase2 a m (by omega),if_neg (by omega),
    show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega,
    show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    show m-1+1=m by omega,
    gp0_T_phase1 a m (by omega),if_pos (by omega)]

theorem fpar_T_phase4 (a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.fpar (T m) 0 ((6*a+4:Nat):Int) 0=(6*a+1:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((6*a+4:Nat):Int)) ((6*a+3:Nat):Int) 0=_
  rw [gp0_T_phase4 a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase3 a m (by omega),if_neg (by omega),
    show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega,
    show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    show m-1+1=m by omega,
    gp0_T_phase2 a m (by omega),if_neg (by omega),
    show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega,
    show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase1 a m (by omega),if_pos (by omega)]

theorem fpar_T_phase5 (a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.fpar (T m) 0 ((6*a+5:Nat):Int) 0=(6*a:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((6*a+5:Nat):Int)-1=((6*a+4:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((6*a+5:Nat):Int)) ((6*a+4:Nat):Int) 0=_
  rw [gp0_T_phase5 a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase4 a m (by omega),if_neg (by omega),
    show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega,
    show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    show m-1+1=m by omega,
    gp0_T_phase3 a m (by omega),if_neg (by omega),
    show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega,
    show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase2 a m (by omega),if_neg (by omega),
    show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega,
    show m-2=(m-3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase1 a m (by omega),if_neg (by omega),
    show ((6*a+1:Nat):Int)-1=((6*a:Nat):Int) by omega,
    show m-3=(m-4)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_T_phase0 a m (by omega),if_pos (by omega)]

def parentT (k : Nat) : Nat :=
  if k%6=0 ∨ k%6=1 ∨ k%6=2 then k-1
  else if k%6=3 then k-2 else if k%6=4 then k-3 else k-5

theorem parentT_lt (k : Nat) (hk : 0<k) : parentT k<k := by
  unfold parentT
  split <;> rename_i h012
  · omega
  split <;> rename_i h3
  · have : 2≤k := by omega
    omega
  split <;> rename_i h4
  · have : 3≤k := by omega
    omega
  · have : 5≤k := by omega
    omega

theorem parentT_phase0 (a : Nat) : parentT (6*(a+1))=6*a+5 := by
  unfold parentT
  rw [if_pos (by omega)]
  omega

theorem parentT_phase1 (a : Nat) : parentT (6*a+1)=6*a := by
  unfold parentT
  rw [if_pos (by omega)]
  omega

theorem parentT_phase2 (a : Nat) : parentT (6*a+2)=6*a+1 := by
  unfold parentT
  rw [if_pos (by omega)]
  omega

theorem parentT_phase3 (a : Nat) : parentT (6*a+3)=6*a+1 := by
  unfold parentT
  rw [if_neg (by omega),if_pos (by omega)]
  omega

theorem parentT_phase4 (a : Nat) : parentT (6*a+4)=6*a+1 := by
  unfold parentT
  rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  omega

theorem parentT_phase5 (a : Nat) : parentT (6*a+5)=6*a := by
  unfold parentT
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  omega

theorem fpar_T_pos (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (T m) 0 (k:Int) 0=(parentT k:Nat) := by
  have hm : k%6=0 ∨ k%6=1 ∨ k%6=2 ∨ k%6=3 ∨ k%6=4 ∨ k%6=5 := by omega
  rcases hm with h0|h1|h2|h3|h4|h5
  · have heq : k=6*((k/6-1)+1) := by omega
    rw [heq]
    rw [parentT_phase0]
    exact fpar_T_phase0 (k/6-1) m (by omega)
  · have heq : k=6*(k/6)+1 := by omega
    rw [heq]
    rw [parentT_phase1]
    exact fpar_T_phase1 (k/6) m (by omega)
  · have heq : k=6*(k/6)+2 := by omega
    rw [heq]
    rw [parentT_phase2]
    exact fpar_T_phase2 (k/6) m (by omega)
  · have heq : k=6*(k/6)+3 := by omega
    rw [heq]
    rw [parentT_phase3]
    exact fpar_T_phase3 (k/6) m (by omega)
  · have heq : k=6*(k/6)+4 := by omega
    rw [heq]
    rw [parentT_phase4]
    exact fpar_T_phase4 (k/6) m (by omega)
  · have heq : k=6*(k/6)+5 := by omega
    rw [heq]
    rw [parentT_phase5]
    exact fpar_T_phase5 (k/6) m (by omega)

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

/-! ### Reduction structure of the complete ladder. -/

def V (m : Nat) : Trans.Recal.PS := [(1,1)]++T m

def R (m : Nat) : Trans.Recal.PS := [(2,1),(2,1),(2,0)]++V m

theorem length_V (m : Nat) : (V m).length=m+1 := by simp [V,length_T]

theorem length_R (m : Nat) : (R m).length=m+4 := by simp [R,length_V]

theorem lenI_R (m : Nat) : Trans.Recal.lenI (R m)=(m:Int)+4 := by
  unfold Trans.Recal.lenI
  rw [length_R]
  omega

theorem drop_two_L (m : Nat) : (L m).drop 2=R m := rfl

theorem fpar0_L_one (m : Nat) : Trans.Recal.fpar0 (L m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar0_L_two (m : Nat) : Trans.Recal.fpar0 (L m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar0_L_one_lb (m : Nat) : Trans.Recal.fpar0 (L m) 1 1=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_one (m : Nat) : Trans.Recal.fpar (L m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 1 0
    if j1<0 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+4) (L m) 1 j1 0)=0
  rw [fpar0_L_one]
  rfl

theorem fpar1_L_two_lb (m : Nat) : Trans.Recal.fpar (L m) 1 2 1=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 2 1
    if j1<1 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+6) (L m) 1 j1 1)=-1
  rw [fpar0_L_two]
  simp only [show ¬((1:Int)<1) by omega,if_false]
  rw [show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_one_lb,if_pos (by omega)]

theorem trMax_L (m : Nat) : Trans.Recal.trMax (L m)=1 := by
  show Trans.Recal.trMaxAux ((L m).length+1) (L m) 0=1
  rw [length_L]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1) 0=true from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1) 0=0 from by simpa using fpar1_L_one m]
    unfold Trans.Recal.lenI
    rw [length_L]
    rw [show decide ((0:Int)<((m+6:Nat):Int))=true from decide_eq_true (by omega)]
    rfl]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1+1) (0+1)=false from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1+1) (0+1)=-1 from by
      simpa using fpar1_L_two_lb m]
    simp,if_pos (by rfl)]
  omega

theorem gp0_R_tail (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (R m) ((k+4:Nat):Int)=p k := by
  show (if (((k+4:Nat):Int)<0) then 0 else ((R m).getD (k+4) (0,0)).1)=p k
  rw [if_neg (by omega)]
  change ((T m).getD k (0,0)).1=p k
  rw [getD_T m k hk]

theorem fpar_R_root (m : Nat) :
    Trans.Recal.fpar (R m) 0 3 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show Trans.Recal.gp0 (R m) 3=1 from rfl]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (3:Int)-1=2 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 2=2 from rfl,if_neg (by omega),
    show (2:Int)-1=1 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 1=2 from rfl,if_neg (by omega),
    show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 0=2 from rfl,if_neg (by omega),
    show (0:Int)-1=-1 by omega,if_pos (by omega)]

theorem fpar_R_tail_zero (m : Nat) (hm : 0<m) :
    Trans.Recal.fpar (R m) 0 4 0=3 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show Trans.Recal.gp0 (R m) 4=2 from by
    simpa only [p_phase0 0] using gp0_R_tail m 0 hm]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar_R_tail_pos (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (R m) 0 ((k+4:Nat):Int) 0=((parentT k+4:Nat):Int) := by
  have hm : k%6=0 ∨ k%6=1 ∨ k%6=2 ∨ k%6=3 ∨ k%6=4 ∨ k%6=5 := by omega
  rcases hm with h0|h1|h2|h3|h4|h5
  all_goals
    unfold Trans.Recal.fpar
    rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  · have heq : k=6*((k/6-1)+1) := by omega
    rw [heq,show parentT (6*((k/6-1)+1))=6*(k/6-1)+5 from by
      simp [parentT]; omega]
    rw [show ((6*((k/6-1)+1)+4:Nat):Int)-1=
      ((6*(k/6-1)+9:Nat):Int) by omega]
    change Trans.Recal.fpar0Aux (m+5) (R m)
      (Trans.Recal.gp0 (R m) ((6*((k/6-1)+1)+4:Nat):Int))
      ((6*(k/6-1)+9:Nat):Int) 0=_
    rw [show Trans.Recal.gp0 (R m) ((6*((k/6-1)+1)+4:Nat):Int)=
        ((2*(k/6-1+1)+2:Nat):Int) from by
          simpa only [show 6*((k/6-1)+1)+4=6*((k/6-1)+1)+4 by rfl,
            p_phase0] using gp0_R_tail m (6*((k/6-1)+1)) (by omega),
      Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6-1)+9:Nat):Int)=
        ((2*(k/6-1)+3:Nat):Int) from by
          simpa only [show 6*(k/6-1)+9=6*(k/6-1)+5+4 by omega,
            p_phase5] using gp0_R_tail m (6*(k/6-1)+5) (by omega),
      if_pos (by omega)]
  · have heq : k=6*(k/6)+1 := by omega
    rw [heq,show parentT (6*(k/6)+1)=6*(k/6) from by simp [parentT]]
    rw [show ((6*(k/6)+1+4:Nat):Int)-1=((6*(k/6)+4:Nat):Int) by omega]
    change Trans.Recal.fpar0Aux (m+5) (R m)
      (Trans.Recal.gp0 (R m) ((6*(k/6)+5:Nat):Int)) ((6*(k/6)+4:Nat):Int) 0=_
    rw [show Trans.Recal.gp0 (R m) ((6*(k/6)+5:Nat):Int)=
        ((2*(k/6)+3:Nat):Int) from by
          simpa only [show 6*(k/6)+5=6*(k/6)+1+4 by omega,p_phase1] using
            gp0_R_tail m (6*(k/6)+1) (by omega),
      Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+4:Nat):Int)=
        ((2*(k/6)+2:Nat):Int) from by
          simpa only [p_phase0] using gp0_R_tail m (6*(k/6)) (by omega),
      if_pos (by omega)]
  · have heq : k=6*(k/6)+2 := by omega
    rw [heq,show parentT (6*(k/6)+2)=6*(k/6)+1 from by simp [parentT]]
    rw [show ((6*(k/6)+2+4:Nat):Int)-1=((6*(k/6)+5:Nat):Int) by omega]
    change Trans.Recal.fpar0Aux (m+5) (R m)
      (Trans.Recal.gp0 (R m) ((6*(k/6)+6:Nat):Int)) ((6*(k/6)+5:Nat):Int) 0=_
    rw [show Trans.Recal.gp0 (R m) ((6*(k/6)+6:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+6=6*(k/6)+2+4 by omega,p_phase2] using
            gp0_R_tail m (6*(k/6)+2) (by omega),
      Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+5:Nat):Int)=
        ((2*(k/6)+3:Nat):Int) from by
          simpa only [show 6*(k/6)+5=6*(k/6)+1+4 by omega,p_phase1] using
            gp0_R_tail m (6*(k/6)+1) (by omega),
      if_pos (by omega)]
  · have heq : k=6*(k/6)+3 := by omega
    rw [heq,show parentT (6*(k/6)+3)=6*(k/6)+1 from by simp [parentT]]
    rw [show ((6*(k/6)+3+4:Nat):Int)-1=((6*(k/6)+6:Nat):Int) by omega]
    change Trans.Recal.fpar0Aux (m+5) (R m)
      (Trans.Recal.gp0 (R m) ((6*(k/6)+7:Nat):Int)) ((6*(k/6)+6:Nat):Int) 0=_
    rw [show Trans.Recal.gp0 (R m) ((6*(k/6)+7:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+7=6*(k/6)+3+4 by omega,p_phase3] using
            gp0_R_tail m (6*(k/6)+3) (by omega),
      Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+6:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+6=6*(k/6)+2+4 by omega,p_phase2] using
            gp0_R_tail m (6*(k/6)+2) (by omega),if_neg (by omega),
      show ((6*(k/6)+6:Nat):Int)-1=((6*(k/6)+5:Nat):Int) by omega,
      show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+5:Nat):Int)=
        ((2*(k/6)+3:Nat):Int) from by
          simpa only [show 6*(k/6)+5=6*(k/6)+1+4 by omega,p_phase1] using
            gp0_R_tail m (6*(k/6)+1) (by omega),if_pos (by omega)]
  · have heq : k=6*(k/6)+4 := by omega
    rw [heq,show parentT (6*(k/6)+4)=6*(k/6)+1 from by simp [parentT]]
    rw [show ((6*(k/6)+4+4:Nat):Int)-1=((6*(k/6)+7:Nat):Int) by omega]
    change Trans.Recal.fpar0Aux (m+5) (R m)
      (Trans.Recal.gp0 (R m) ((6*(k/6)+8:Nat):Int)) ((6*(k/6)+7:Nat):Int) 0=_
    rw [show Trans.Recal.gp0 (R m) ((6*(k/6)+8:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+8=6*(k/6)+4+4 by omega,p_phase4] using
            gp0_R_tail m (6*(k/6)+4) (by omega),
      Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+7:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+7=6*(k/6)+3+4 by omega,p_phase3] using
            gp0_R_tail m (6*(k/6)+3) (by omega),if_neg (by omega),
      show ((6*(k/6)+7:Nat):Int)-1=((6*(k/6)+6:Nat):Int) by omega,
      show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+6:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+6=6*(k/6)+2+4 by omega,p_phase2] using
            gp0_R_tail m (6*(k/6)+2) (by omega),if_neg (by omega),
      show ((6*(k/6)+6:Nat):Int)-1=((6*(k/6)+5:Nat):Int) by omega,
      show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+5:Nat):Int)=
        ((2*(k/6)+3:Nat):Int) from by
          simpa only [show 6*(k/6)+5=6*(k/6)+1+4 by omega,p_phase1] using
            gp0_R_tail m (6*(k/6)+1) (by omega),if_pos (by omega)]
  · have heq : k=6*(k/6)+5 := by omega
    rw [heq,show parentT (6*(k/6)+5)=6*(k/6) from by simp [parentT]]
    rw [show ((6*(k/6)+5+4:Nat):Int)-1=((6*(k/6)+8:Nat):Int) by omega]
    change Trans.Recal.fpar0Aux (m+5) (R m)
      (Trans.Recal.gp0 (R m) ((6*(k/6)+9:Nat):Int)) ((6*(k/6)+8:Nat):Int) 0=_
    rw [show Trans.Recal.gp0 (R m) ((6*(k/6)+9:Nat):Int)=
        ((2*(k/6)+3:Nat):Int) from by
          simpa only [show 6*(k/6)+9=6*(k/6)+5+4 by omega,p_phase5] using
            gp0_R_tail m (6*(k/6)+5) (by omega),
      Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+8:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+8=6*(k/6)+4+4 by omega,p_phase4] using
            gp0_R_tail m (6*(k/6)+4) (by omega),if_neg (by omega),
      show ((6*(k/6)+8:Nat):Int)-1=((6*(k/6)+7:Nat):Int) by omega,
      show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+7:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+7=6*(k/6)+3+4 by omega,p_phase3] using
            gp0_R_tail m (6*(k/6)+3) (by omega),if_neg (by omega),
      show ((6*(k/6)+7:Nat):Int)-1=((6*(k/6)+6:Nat):Int) by omega,
      show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+6:Nat):Int)=
        ((2*(k/6)+4:Nat):Int) from by
          simpa only [show 6*(k/6)+6=6*(k/6)+2+4 by omega,p_phase2] using
            gp0_R_tail m (6*(k/6)+2) (by omega),if_neg (by omega),
      show ((6*(k/6)+6:Nat):Int)-1=((6*(k/6)+5:Nat):Int) by omega,
      show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+5:Nat):Int)=
        ((2*(k/6)+3:Nat):Int) from by
          simpa only [show 6*(k/6)+5=6*(k/6)+1+4 by omega,p_phase1] using
            gp0_R_tail m (6*(k/6)+1) (by omega),if_neg (by omega),
      show ((6*(k/6)+5:Nat):Int)-1=((6*(k/6)+4:Nat):Int) by omega,
      show m+1=m+1 by rfl,Trans.Recal.fpar0Aux,if_neg (by omega),
      show Trans.Recal.gp0 (R m) ((6*(k/6)+4:Nat):Int)=
        ((2*(k/6)+2:Nat):Int) from by
          simpa only [p_phase0] using gp0_R_tail m (6*(k/6)) (by omega),
      if_pos (by omega)]

theorem fAncAux_R_tail_last (k : Nat) : ∀ m f : Nat, ∀ acc : List Int,
    k<m → k+4<f → acc.getLast?=some ((k+4:Nat):Int) →
    (Trans.Recal.fAncAux f (R m) 0 ((k+4:Nat):Int) 0 acc).getLast?=some 3 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, ∀ acc:List Int,
    k<m → k+4<f → acc.getLast?=some ((k+4:Nat):Int) →
    (Trans.Recal.fAncAux f (R m) 0 ((k+4:Nat):Int) 0 acc).getLast?=some 3) k ?_
  intro k ih m f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      rw [show ((0+4:Nat):Int)=4 from by omega,fpar_R_tail_zero m (by omega),
        if_pos (by omega)]
      cases f with
      | zero => omega
      | succ f =>
        simp only [Trans.Recal.fAncAux]
        rw [fpar_R_root,if_neg (by omega)]
        simp
    · have hkpos:0<k:=by omega
      rw [fpar_R_tail_pos m k hkpos hkm,if_pos (by omega)]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk m f
        (acc++[((parentT k+4:Nat):Int)])
        (by exact Nat.lt_trans hpk hkm) (by omega) (by simp)

theorem fAnc_R_tail_last (m : Nat) (hm : 0<m) :
    (Trans.Recal.fAnc (R m) 0 ((m+3:Nat):Int) 0).getLast?=some 3 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  have h:=fAncAux_R_tail_last (m-1) m (m+5) [((m-1+4:Nat):Int)]
    (by omega) (by omega) (by simp)
  simpa only [show m-1+4=m+3 by omega] using h

theorem slice_R_tail (m : Nat) :
    Trans.Recal.slice (R m) 3 ((m+4:Nat):Int)=V m := by
  unfold Trans.Recal.slice R
  change (V m).take ((((m+4:Nat):Int)-3).toNat)=V m
  rw [show ((((m+4:Nat):Int)-3).toNat)=m+1 by omega]
  simpa only [length_V] using (List.take_length (l:=V m))

theorem fpar_R_zero (m : Nat) : Trans.Recal.fpar (R m) 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar_R_one (m : Nat) : Trans.Recal.fpar (R m) 0 1 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show Trans.Recal.gp0 (R m) 1=2 from rfl]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 0=2 from rfl,if_neg (by omega),
    show (0:Int)-1=-1 by omega,if_pos (by omega)]

theorem fpar_R_two (m : Nat) : Trans.Recal.fpar (R m) 0 2 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show Trans.Recal.gp0 (R m) 2=2 from rfl]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (2:Int)-1=1 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 1=2 from rfl,if_neg (by omega),
    show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 0=2 from rfl,if_neg (by omega),
    show (0:Int)-1=-1 by omega,if_pos (by omega)]

theorem fAnc_R_zero (m : Nat) : Trans.Recal.fAnc (R m) 0 0 0=[0] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  simp only [Trans.Recal.fAncAux]
  rw [fpar_R_zero,if_neg (by omega)]

theorem fAnc_R_one (m : Nat) : Trans.Recal.fAnc (R m) 0 1 0=[1] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  simp only [Trans.Recal.fAncAux]
  rw [fpar_R_one,if_neg (by omega)]

theorem fAnc_R_two (m : Nat) : Trans.Recal.fAnc (R m) 0 2 0=[2] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  simp only [Trans.Recal.fAncAux]
  rw [fpar_R_two,if_neg (by omega)]

theorem slice_R_zero (m : Nat) : Trans.Recal.slice (R m) 0 1=[(2,1)] := by rfl
theorem slice_R_one (m : Nat) : Trans.Recal.slice (R m) 1 2=[(2,1)] := by rfl
theorem slice_R_two (m : Nat) : Trans.Recal.slice (R m) 2 3=[(2,0)] := by rfl

theorem fAnc_R_last (m : Nat) :
    (Trans.Recal.fAnc (R m) 0 ((m+3:Nat):Int) 0).getLast?=some 3 := by
  cases m with
  | zero => decide
  | succ m => exact fAnc_R_tail_last (m+1) (by omega)

theorem ppair_R (m : Nat) :
    Trans.Recal.ppair (R m)=[[(2,1)],[(2,1)],[(2,0)],V m] := by
  unfold Trans.Recal.ppair
  rw [length_R,lenI_R]
  rw [show m+4+1=m+5 by omega]
  rw [show (m:Int)+4-1=((m+3:Nat):Int) by omega]
  rw [show m+5=(m+4)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega)]
  dsimp only
  have hf := fAnc_R_last m
  rw [hf]
  simp only [Option.getD_some]
  have hs : Trans.Recal.slice (R m) 3 (((m+3:Nat):Int)+1)=V m := by
    simpa only [show ((m+3:Nat):Int)+1=((m+4:Nat):Int) by omega] using
      slice_R_tail m
  rw [show (3:Int)-1=2 by omega,hs]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_R_two]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (2:Int)-1=1 by omega,show (2:Int)+1=3 by omega,slice_R_two]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_R_one]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (1:Int)-1=0 by omega,show (1:Int)+1=2 by omega,slice_R_one]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_R_zero]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (0:Int)-1=-1 by omega,show (0:Int)+1=1 by omega,slice_R_zero]
  rw [Trans.Recal.ppairAux,if_pos (by omega)]

theorem brF_L (m : Nat) :
    Trans.Recal.brF (L m)=[[(2,1)],[(2,1)],[(2,0)],V m] := by
  unfold Trans.Recal.brF
  rw [trMax_L]
  change Trans.Recal.ppair ((L m).drop 2)=_
  rw [drop_two_L]
  exact ppair_R m

theorem firstNodes_L (m : Nat) :
    Trans.Recal.firstNodes (L m)=[2,3,4,5,((m+6:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L,trMax_L]
  simp only [List.foldl_cons,List.foldl_nil,length_V,List.map_cons,List.map_nil]
  simp
  push_cast
  omega

theorem joints_L (m : Nat) : Trans.Recal.joints (L m)=[1,1,1,0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_L]
  change [Trans.Recal.fpar (L m) 0 2 0,
    Trans.Recal.fpar (L m) 0 3 0,Trans.Recal.fpar (L m) 0 4 0,
    Trans.Recal.fpar (L m) 0 5 0]=[1,1,1,0]
  rw [fpar_L_base_two,fpar_L_base_three,fpar_L_base_four,
    fpar_L_base_five]

theorem fpar1_L_two (m : Nat) : Trans.Recal.fpar (L m) 1 2 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  rw [show Trans.Recal.gp1 (L m) 2=1 from rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) 2 0=1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rfl]
  rw [if_neg (by omega),show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  rw [fpar0_L_one,if_neg (by omega),
    show Trans.Recal.gp1 (L m) 0=0 from rfl,if_pos (by omega)]

theorem fpar1_L_three (m : Nat) : Trans.Recal.fpar (L m) 1 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  rw [show Trans.Recal.gp1 (L m) 3=1 from rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) 3 0=1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rfl]
  rw [if_neg (by omega),show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  rw [fpar0_L_one,if_neg (by omega),
    show Trans.Recal.gp1 (L m) 0=0 from rfl,if_pos (by omega)]

/-! ### Six-phase reduction. -/

/-- A uniformly shifted copy of the periodic tail. -/
def TS (d : Int) (m : Nat) : Trans.Recal.PS :=
  Trans.Recal.incrFirst (T m) d

/-- The canonical tail obtained after removing the initial row-zero gap. -/
def S (m : Nat) : Trans.Recal.PS := TS (-2) m

/-- Four mutually recurring reduction states.  The parameter records the
uniform row-zero excess; one complete six-column block increments it once. -/
def J (d m : Nat) : Trans.Recal.PS := [(1,1)]++TS d m
def Q (d m : Nat) : Trans.Recal.PS := [(0,0),(2,1)]++TS (d+1) m
def N (d m : Nat) : Trans.Recal.PS :=
  [(2,0)]++Trans.Recal.derp (TS d m)
def K (d m : Nat) : Trans.Recal.PS :=
  [(0,0)]++Trans.Recal.derp (TS ((d:Int)-1) m)

def A (r e : Int) (m : Nat) : Trans.Recal.PS :=
  [(r,0)]++Trans.Recal.derp (TS e m)

theorem N_eq_A (d m : Nat) : N d m=A 2 d m := rfl
theorem K_eq_A (d m : Nat) : K d m=A 0 ((d:Int)-1) m := rfl

theorem incrFirst_incrFirst (M : Trans.Recal.PS) (a b : Int) :
    Trans.Recal.incrFirst (Trans.Recal.incrFirst M a) b=
      Trans.Recal.incrFirst M (a+b) := by
  unfold Trans.Recal.incrFirst
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  apply Prod.ext <;> simp <;> omega

theorem incrFirst_zero (M : Trans.Recal.PS) :
    Trans.Recal.incrFirst M 0=M := by
  unfold Trans.Recal.incrFirst
  simpa only [Int.add_zero] using List.map_id (l:=M)

theorem incrFirst_TS (d e : Int) (m : Nat) :
    Trans.Recal.incrFirst (TS d m) e=TS (d+e) m := by
  exact incrFirst_incrFirst (T m) d e

theorem incrFirst_derp (M : Trans.Recal.PS) (d : Int) :
    Trans.Recal.incrFirst (Trans.Recal.derp M) d=
      Trans.Recal.derp (Trans.Recal.incrFirst M d) := by
  unfold Trans.Recal.incrFirst Trans.Recal.derp
  exact List.map_drop

theorem length_TS (d : Int) (m : Nat) : (TS d m).length=m := by
  simp [TS,length_T,Trans.Recal.incrFirst]

theorem lenI_TS (d : Int) (m : Nat) : Trans.Recal.lenI (TS d m)=(m:Int) := by
  unfold Trans.Recal.lenI
  rw [length_TS]

theorem length_J (d m : Nat) : (J d m).length=m+1 := by
  simp [J,length_TS]

theorem length_Q (d m : Nat) : (Q d m).length=m+2 := by
  simp [Q,length_TS]

theorem length_N (d m : Nat) (hm : 0<m) : (N d m).length=m := by
  unfold N Trans.Recal.derp
  rw [List.length_append,List.length_singleton,List.length_drop,length_TS]
  omega

theorem length_K (d m : Nat) (hm : 0<m) : (K d m).length=m := by
  unfold K Trans.Recal.derp
  rw [List.length_append,List.length_singleton,List.length_drop,length_TS]
  omega

theorem p_add_six (k : Nat) : p (k+6)=p k+2 := by
  unfold p
  rw [show (k+6)%6=k%6 by omega,show (k+6)/6=k/6+1 by omega]
  split <;> rename_i h0
  · push_cast
    omega
  split <;> push_cast <;> omega

theorem q_add_six (k : Nat) : q (k+6)=q k := by
  unfold q
  rw [show (k+6)%6=k%6 by omega]

theorem TS_succ (d : Int) (m : Nat) :
    TS d (m+1)=TS d m++[(p m+d,q m)] := by
  unfold TS Trans.Recal.incrFirst
  rw [T_succ,List.map_append]
  rfl

theorem S_succ (m : Nat) : S (m+1)=S m++[(p m-2,q m)] := by
  exact TS_succ (-2) m

theorem S_zero : S 0=[] := rfl
theorem S_one : S 1=Trans.Recal.zeroPS := rfl
theorem S_two : S 2=G1.LG 0 := rfl
theorem S_three : S 3=G1.LG 1 := rfl
theorem S_four : S 4=G1.LG 2 := rfl
theorem S_five : S 5=G9.L 0 := rfl
theorem S_six : S 6=L 0 := rfl

theorem S_add_six : ∀ m : Nat, S (m+6)=L m
  | 0 => rfl
  | m+1 => by
    rw [show m+1+6=(m+6)+1 by omega,S_succ,S_add_six m,L_succ]
    congr 1
    apply congrArg (fun x => [x])
    apply Prod.ext
    · rw [p_add_six]
      omega
    · exact q_add_six m

theorem J_zero_shift (m : Nat) : J 0 m=V m := by
  unfold J V
  rw [show TS (0:Nat) m=T m from by
    unfold TS
    change Trans.Recal.incrFirst (T m) 0=T m
    exact incrFirst_zero _]

theorem Q_from_J (d m : Nat) :
    Trans.Recal.jjSeq 0 0++Trans.Recal.incrFirst (J d m) 1=Q d m := by
  unfold J Q
  unfold Trans.Recal.incrFirst
  simp only [List.map_append,List.map_cons,List.map_nil]
  change [(0,0)]++([(2,1)]++Trans.Recal.incrFirst (TS (d:Int) m) 1)=
    [(0,0),(2,1)]++TS ((d+1:Nat):Int) m
  rw [incrFirst_TS,show (d:Int)+1=((d+1:Nat):Int) by omega]
  simp

theorem K_from_N (d m : Nat) :
    Trans.Recal.incrFirst (N (d+1) m) (-2)=K d m := by
  unfold N K
  unfold Trans.Recal.incrFirst
  simp only [List.map_append,List.map_cons,List.map_nil]
  change [(0,0)]++Trans.Recal.incrFirst (Trans.Recal.derp (TS ((d+1:Nat):Int) m)) (-2)=
    [(0,0)]++Trans.Recal.derp (TS ((d:Int)-1) m)
  rw [incrFirst_derp,incrFirst_TS,
    show ((d+1:Nat):Int)+(-2)=(d:Int)-1 by omega]

/-! Uniform shifts preserve the row-zero parent tree of `T`. -/

theorem fpar_TS_pos (d : Int) (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (TS d m) 0 (k:Int) 0=(parentT k:Nat) := by
  unfold TS
  rw [Evidence.Cert.fpar_row0_incrFirst (T m) d (k:Int) 0
    (by omega) (by omega) (by rw [lenI_T]; omega)]
  exact fpar_T_pos m k hk0 hk

theorem isAncAux_TS (d : Int) (k : Nat) : ∀ m f : Nat, k<m → k<f →
    Trans.Recal.isAncAux f (TS d m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, k<m → k<f →
    Trans.Recal.isAncAux f (TS d m) 0 (k:Int) 0=true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_TS_pos d m k (by omega) hkm]
      rw [show (((parentT k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hp:=parentT_lt k (by omega)
      exact ih (parentT k) hp m f (by omega) (by omega)

theorem isAnc_TS (d : Int) (m k : Nat) (hk : k<m) :
    Trans.Recal.isAnc (TS d m) 0 (k:Int) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_TS]; omega),length_TS]
  exact isAncAux_TS d k m (m+1) hk (by omega)

theorem fAncAux_TS_last (d : Int) (k : Nat) : ∀ m f : Nat,
    ∀ acc : List Int, k<m → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (TS d m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, ∀ acc:List Int,
    k<m → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (TS d m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih m f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      have hp : Trans.Recal.fpar (TS d m) 0 0 0=-1 := by
        unfold Trans.Recal.fpar
        rw [if_neg (by rw [lenI_TS]; omega),if_pos (by rfl)]
        simp only [Trans.Recal.fpar0Aux]
        rw [if_pos (by omega)]
      rw [show ((0:Nat):Int)=0 from rfl,hp,if_neg (by omega)]
      exact hlast
    · rw [fpar_TS_pos d m k (by omega) hkm,if_pos (by omega)]
      have hp:=parentT_lt k (by omega)
      exact ih (parentT k) hp m f (acc++[((parentT k:Nat):Int)])
        (by omega) (by omega) (by simp)

theorem fAnc_TS_last (d : Int) (m : Nat) (hm : 0<m) :
    (Trans.Recal.fAnc (TS d m) 0 ((m-1:Nat):Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_TS]; omega),length_TS]
  exact fAncAux_TS_last d (m-1) m (m+1) [((m-1:Nat):Int)]
    (by omega) (by omega) (by simp)

theorem slice_TS_full (d : Int) (m : Nat) :
    Trans.Recal.slice (TS d m) 0 (m:Int)=TS d m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show ((m:Int)-0).toNat=m by omega]
  simpa only [length_TS] using (List.take_length (l:=TS d m))

theorem ppair_TS (d : Int) : ∀ m : Nat,
    Trans.Recal.ppair (TS d m)=if m=0 then [] else [TS d m]
  | 0 => rfl
  | m+1 => by
    unfold Trans.Recal.ppair
    rw [length_TS]
    simp only [show ¬m+1=0 by omega,if_false,Trans.Recal.ppairAux]
    rw [show Trans.Recal.lenI (TS d (m+1))-1=(m:Int) by
      rw [lenI_TS]; omega,if_neg (by omega)]
    have hf : (Trans.Recal.fAnc (TS d (m+1)) 0 (m:Int) 0).getLast?=some 0 := by
      simpa only [Nat.add_sub_cancel] using fAnc_TS_last d (m+1) (by omega)
    rw [hf]
    simp only [Option.getD_some]
    rw [show (0:Int)-1=-1 by omega,if_pos (by omega),
      show (m:Int)+1=((m+1:Nat):Int) by omega,slice_TS_full]

theorem gp0_TS (d : Int) (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (TS d m) (k:Int)=p k+d := by
  unfold TS
  rw [Evidence.Cert.gp0_incrFirst_of_valid (T m) d (k:Int)
    (by omega) (by simpa only [length_T] using hk)]
  rw [gp0_T m k hk]

theorem gp1_TS (d : Int) (m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (TS d m) (k:Int)=q k := by
  show (if (k:Int)<0 then 0 else ((TS d m).getD k (0,0)).2)=q k
  rw [if_neg (by omega)]
  unfold TS Trans.Recal.incrFirst
  rw [List.getD_eq_getElem?_getD,List.getElem?_map]
  have hkT : k<(T m).length := by simpa only [length_T] using hk
  have he : (T m)[k]?=some ((T m).getD k (0,0)) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hkT]
    simp
  rw [he]
  simp only [Option.map_some,Option.getD_some]
  rw [getD_T m k hk]

/-! The aligned state shared by `N` and `K`. -/

theorem length_A (r e : Int) (m : Nat) (hm : 0<m) : (A r e m).length=m := by
  unfold A Trans.Recal.derp
  rw [List.length_append,List.length_singleton,List.length_drop,length_TS]
  omega

theorem lenI_A (r e : Int) (m : Nat) (hm : 0<m) :
    Trans.Recal.lenI (A r e m)=(m:Int) := by
  unfold Trans.Recal.lenI
  rw [length_A r e m hm]

theorem gp0_A_zero (r e : Int) (m : Nat) :
    Trans.Recal.gp0 (A r e m) 0=r := by rfl

theorem gp1_A_zero (r e : Int) (m : Nat) :
    Trans.Recal.gp1 (A r e m) 0=0 := by rfl

theorem gp0_A_pos (r e : Int) (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.gp0 (A r e m) (k:Int)=p k+e := by
  show (if (k:Int)<0 then 0 else ((A r e m).getD k (0,0)).1)=_
  rw [if_neg (by omega)]
  have hget : (A r e m).getD k (0,0)=(TS e m).getD k (0,0) := by
    cases k with
    | zero => omega
    | succ k =>
      unfold A Trans.Recal.derp
      simp only [List.singleton_append]
      rw [List.getD_cons_succ,List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD,List.getElem?_drop]
      rw [show 1+k=k+1 by omega]
  rw [hget]
  have h:=gp0_TS e m k hk
  unfold Trans.Recal.gp0 at h
  rw [if_neg (by omega)] at h
  exact h

theorem gp1_A_pos (r e : Int) (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.gp1 (A r e m) (k:Int)=q k := by
  show (if (k:Int)<0 then 0 else ((A r e m).getD k (0,0)).2)=_
  rw [if_neg (by omega)]
  have hget : (A r e m).getD k (0,0)=(TS e m).getD k (0,0) := by
    cases k with
    | zero => omega
    | succ k =>
      unfold A Trans.Recal.derp
      simp only [List.singleton_append]
      rw [List.getD_cons_succ,List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD,List.getElem?_drop]
      rw [show 1+k=k+1 by omega]
  rw [hget]
  have h:=gp1_TS e m k hk
  unfold Trans.Recal.gp1 at h
  rw [if_neg (by omega)] at h
  exact h

theorem gp0_A_phase0 (r e : Int) (a m : Nat) (ha : 0<a) (h : 6*a<m) :
    Trans.Recal.gp0 (A r e m) ((6*a:Nat):Int)=((2*a+2:Nat):Int)+e := by
  simpa only [p_phase0 a] using gp0_A_pos r e m (6*a) (by omega) h

theorem gp0_A_phase1 (r e : Int) (a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.gp0 (A r e m) ((6*a+1:Nat):Int)=
      ((2*a+3:Nat):Int)+e := by
  simpa only [p_phase1 a] using gp0_A_pos r e m (6*a+1) (by omega) h

theorem gp0_A_phase2 (r e : Int) (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.gp0 (A r e m) ((6*a+2:Nat):Int)=
      ((2*a+4:Nat):Int)+e := by
  simpa only [p_phase2 a] using gp0_A_pos r e m (6*a+2) (by omega) h

theorem gp0_A_phase3 (r e : Int) (a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.gp0 (A r e m) ((6*a+3:Nat):Int)=
      ((2*a+4:Nat):Int)+e := by
  simpa only [p_phase3 a] using gp0_A_pos r e m (6*a+3) (by omega) h

theorem gp0_A_phase4 (r e : Int) (a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.gp0 (A r e m) ((6*a+4:Nat):Int)=
      ((2*a+4:Nat):Int)+e := by
  simpa only [p_phase4 a] using gp0_A_pos r e m (6*a+4) (by omega) h

theorem gp0_A_phase5 (r e : Int) (a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.gp0 (A r e m) ((6*a+5:Nat):Int)=
      ((2*a+3:Nat):Int)+e := by
  simpa only [p_phase5 a] using gp0_A_pos r e m (6*a+5) (by omega) h

theorem fpar_A_phase0 (r e : Int) (a m : Nat) (h : 6*(a+1)<m) :
    Trans.Recal.fpar (A r e m) 0 ((6*(a+1):Nat):Int) 0=
      ((6*a+5:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),if_pos (by rfl),
    length_A r e m (by omega)]
  rw [show ((6*(a+1):Nat):Int)-1=((6*a+5:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (A r e m)
    (Trans.Recal.gp0 (A r e m) ((6*(a+1):Nat):Int))
    ((6*a+5:Nat):Int) 0=_
  rw [gp0_A_phase0 r e (a+1) m (by omega) h,
    Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase5 r e a m (by omega),if_pos (by omega)]

theorem fpar_A_phase1_zero (r e : Int) (m : Nat) (hr : r<3+e)
    (hm : 1<m) : Trans.Recal.fpar (A r e m) 0 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),if_pos (by rfl),
    length_A r e m (by omega)]
  rw [show Trans.Recal.gp0 (A r e m) 1=3+e from by
    simpa only using gp0_A_phase1 r e 0 m (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (1:Int)-1=0 by omega,if_neg (by omega),gp0_A_zero,if_pos (by omega)]

theorem fpar_A_phase1_succ (r e : Int) (a m : Nat) (h : 6*(a+1)+1<m) :
    Trans.Recal.fpar (A r e m) 0 ((6*(a+1)+1:Nat):Int) 0=
      ((6*(a+1):Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),if_pos (by rfl),
    length_A r e m (by omega)]
  rw [show ((6*(a+1)+1:Nat):Int)-1=((6*(a+1):Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (A r e m)
    (Trans.Recal.gp0 (A r e m) ((6*(a+1)+1:Nat):Int))
    ((6*(a+1):Nat):Int) 0=_
  rw [gp0_A_phase1 r e (a+1) m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase0 r e (a+1) m (by omega) (by omega),if_pos (by omega)]

theorem fpar_A_phase2 (r e : Int) (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.fpar (A r e m) 0 ((6*a+2:Nat):Int) 0=
      ((6*a+1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),if_pos (by rfl),
    length_A r e m (by omega)]
  rw [show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (A r e m)
    (Trans.Recal.gp0 (A r e m) ((6*a+2:Nat):Int))
    ((6*a+1:Nat):Int) 0=_
  rw [gp0_A_phase2 r e a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase1 r e a m (by omega),if_pos (by omega)]

theorem fpar_A_phase3 (r e : Int) (a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.fpar (A r e m) 0 ((6*a+3:Nat):Int) 0=
      ((6*a+1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),if_pos (by rfl),
    length_A r e m (by omega)]
  rw [show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (A r e m)
    (Trans.Recal.gp0 (A r e m) ((6*a+3:Nat):Int))
    ((6*a+2:Nat):Int) 0=_
  rw [gp0_A_phase3 r e a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase2 r e a m (by omega),if_neg (by omega),
    show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase1 r e a (m-1+1) (by omega),if_pos (by omega)]

theorem fpar_A_phase4 (r e : Int) (a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.fpar (A r e m) 0 ((6*a+4:Nat):Int) 0=
      ((6*a+1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),if_pos (by rfl),
    length_A r e m (by omega)]
  rw [show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (A r e m)
    (Trans.Recal.gp0 (A r e m) ((6*a+4:Nat):Int))
    ((6*a+3:Nat):Int) 0=_
  rw [gp0_A_phase4 r e a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase3 r e a m (by omega),if_neg (by omega),
    show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase2 r e a (m-1+1) (by omega),if_neg (by omega),
    show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega]
  rw [show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase1 r e a ((m-2+1)+1) (by omega),if_pos (by omega)]

theorem fpar_A_phase5 (r e : Int) (a m : Nat) (hr : r<3+e)
    (h : 6*a+5<m) :
    Trans.Recal.fpar (A r e m) 0 ((6*a+5:Nat):Int) 0=((6*a:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),if_pos (by rfl),
    length_A r e m (by omega)]
  rw [show ((6*a+5:Nat):Int)-1=((6*a+4:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (A r e m)
    (Trans.Recal.gp0 (A r e m) ((6*a+5:Nat):Int))
    ((6*a+4:Nat):Int) 0=_
  rw [gp0_A_phase5 r e a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase4 r e a m (by omega),if_neg (by omega),
    show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase3 r e a (m-1+1) (by omega),if_neg (by omega),
    show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  rw [show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase2 r e a ((m-2+1)+1) (by omega),if_neg (by omega),
    show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega]
  rw [show m-2=(m-3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_A_phase1 r e a (((m-3+1)+1)+1) (by omega),if_neg (by omega)]
  rw [show ((6*a+1:Nat):Int)-1=((6*a:Nat):Int) by omega]
  rw [show m-3=(m-4)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega)]
  by_cases ha : a=0
  · subst a
    change (if Trans.Recal.gp0
      (A r e (m-4+1+1+1+1)) 0<3+e then (0:Int) else _)=0
    rw [gp0_A_zero,if_pos hr]
  · rw [gp0_A_phase0 r e a ((((m-4+1)+1)+1)+1) (by omega) (by omega),
      if_pos (by omega)]

theorem fpar_A_pos (r e : Int) (m k : Nat) (hr : r<3+e)
    (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (A r e m) 0 (k:Int) 0=(parentT k:Nat) := by
  have hp : k%6=0∨k%6=1∨k%6=2∨k%6=3∨k%6=4∨k%6=5 := by omega
  rcases hp with h0|h1|h2|h3|h4|h5
  · have he : k=6*((k/6-1)+1) := by omega
    rw [he,parentT_phase0]
    exact fpar_A_phase0 r e (k/6-1) m (by omega)
  · have he : k=6*(k/6)+1 := by omega
    rw [he,parentT_phase1]
    by_cases ha : k/6=0
    · rw [ha]
      exact fpar_A_phase1_zero r e m hr (by omega)
    · have heq : k/6=(k/6-1)+1 := by omega
      rw [heq]
      exact fpar_A_phase1_succ r e (k/6-1) m (by omega)
  · have he : k=6*(k/6)+2 := by omega
    rw [he,parentT_phase2]
    exact fpar_A_phase2 r e (k/6) m (by omega)
  · have he : k=6*(k/6)+3 := by omega
    rw [he,parentT_phase3]
    exact fpar_A_phase3 r e (k/6) m (by omega)
  · have he : k=6*(k/6)+4 := by omega
    rw [he,parentT_phase4]
    exact fpar_A_phase4 r e (k/6) m (by omega)
  · have he : k=6*(k/6)+5 := by omega
    rw [he,parentT_phase5]
    exact fpar_A_phase5 r e (k/6) m hr (by omega)

theorem isAncAux_A (r e : Int) (k : Nat) : ∀ m f : Nat,
    r<3+e → k<m → k<f →
    Trans.Recal.isAncAux f (A r e m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat,
    r<3+e → k<m → k<f →
    Trans.Recal.isAncAux f (A r e m) 0 (k:Int) 0=true) k ?_
  intro k ih m f hr hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_A_pos r e m k hr (by omega) hkm]
      rw [show (((parentT k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hp:=parentT_lt k (by omega)
      exact ih (parentT k) hp m f hr (by omega) (by omega)

theorem isPrincipalP_A (r e : Int) (m : Nat) (hr : r<3+e) (hm : 1<m) :
    Trans.Recal.isPrincipalP (A r e m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (A r e m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_A r e m (by omega)]
    rw [show (m==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
    rfl]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_A r e m (by omega)]; omega),
    length_A r e m (by omega)]
  rw [show Trans.Recal.lenI (A r e m)-1=((m-1:Nat):Int) from by
    rw [lenI_A r e m (by omega)]; omega]
  exact isAncAux_A r e (m-1) m (m+1) hr (by omega) (by omega)

theorem isPrincipalP_N (d m : Nat) (hm : 1<m) :
    Trans.Recal.isPrincipalP (N d m)=true := by
  rw [N_eq_A]
  exact isPrincipalP_A 2 d m (by omega) hm

theorem isPrincipalP_K (d m : Nat) (hm : 1<m) :
    Trans.Recal.isPrincipalP (K d m)=true := by
  rw [K_eq_A]
  exact isPrincipalP_A 0 ((d:Int)-1) m (by omega) hm

theorem gp0_Q_tail (d m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (Q d m) ((k+2:Nat):Int)=p k+(d+1:Int) := by
  show (if ((k+2:Nat):Int)<0 then 0 else
    ((Q d m).getD (k+2) (0,0)).1)=_
  rw [if_neg (by omega)]
  change ((TS ((d+1:Nat):Int) m).getD k (0,0)).1=_
  have h:=gp0_TS ((d+1:Nat):Int) m k hk
  unfold Trans.Recal.gp0 at h
  rw [if_neg (by omega)] at h
  exact h

theorem gp1_Q_tail (d m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (Q d m) ((k+2:Nat):Int)=q k := by
  show (if ((k+2:Nat):Int)<0 then 0 else
    ((Q d m).getD (k+2) (0,0)).2)=_
  rw [if_neg (by omega)]
  change ((TS ((d+1:Nat):Int) m).getD k (0,0)).2=_
  have h:=gp1_TS ((d+1:Nat):Int) m k hk
  unfold Trans.Recal.gp1 at h
  rw [if_neg (by omega)] at h
  exact h

theorem fpar_Q_zero (d m : Nat) :
    Trans.Recal.fpar (Q d m) 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar_Q_one (d m : Nat) :
    Trans.Recal.fpar (Q d m) 0 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [show Trans.Recal.gp0 (Q d m) 1=2 from rfl]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar_Q_tail_zero (d m : Nat) (hm : 0<m) :
    Trans.Recal.fpar (Q d m) 0 2 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [show Trans.Recal.gp0 (Q d m) 2=2+(d+1:Int) from by
    simpa only [p_phase0 0] using gp0_Q_tail d m 0 hm]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (2:Int)-1=1 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (Q d m) 1=2 from rfl,
    if_pos (by omega)]

theorem gp0_Q_phase0 (d a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp0 (Q d m) ((6*a+2:Nat):Int)=
      ((2*a+2:Nat):Int)+(d+1:Int) := by
  simpa only [p_phase0 a] using gp0_Q_tail d m (6*a) h

theorem gp0_Q_phase1 (d a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.gp0 (Q d m) ((6*a+3:Nat):Int)=
      ((2*a+3:Nat):Int)+(d+1:Int) := by
  simpa only [show 6*a+1+2=6*a+3 by omega,p_phase1 a] using
    gp0_Q_tail d m (6*a+1) h

theorem gp0_Q_phase2 (d a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.gp0 (Q d m) ((6*a+4:Nat):Int)=
      ((2*a+4:Nat):Int)+(d+1:Int) := by
  simpa only [show 6*a+2+2=6*a+4 by omega,p_phase2 a] using
    gp0_Q_tail d m (6*a+2) h

theorem gp0_Q_phase3 (d a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.gp0 (Q d m) ((6*a+5:Nat):Int)=
      ((2*a+4:Nat):Int)+(d+1:Int) := by
  simpa only [show 6*a+3+2=6*a+5 by omega,p_phase3 a] using
    gp0_Q_tail d m (6*a+3) h

theorem gp0_Q_phase4 (d a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.gp0 (Q d m) ((6*a+6:Nat):Int)=
      ((2*a+4:Nat):Int)+(d+1:Int) := by
  simpa only [show 6*a+4+2=6*a+6 by omega,p_phase4 a] using
    gp0_Q_tail d m (6*a+4) h

theorem gp0_Q_phase5 (d a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.gp0 (Q d m) ((6*a+7:Nat):Int)=
      ((2*a+3:Nat):Int)+(d+1:Int) := by
  simpa only [show 6*a+5+2=6*a+7 by omega,p_phase5 a] using
    gp0_Q_tail d m (6*a+5) h

theorem fpar_Q_phase0 (d a m : Nat) (h : 6*(a+1)<m) :
    Trans.Recal.fpar (Q d m) 0 ((6*(a+1)+2:Nat):Int) 0=
      ((6*a+7:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [length_Q]
  rw [show ((6*(a+1)+2:Nat):Int)-1=((6*a+7:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+3) (Q d m)
    (Trans.Recal.gp0 (Q d m) ((6*(a+1)+2:Nat):Int))
    ((6*a+7:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (Q d m) ((6*(a+1)+2:Nat):Int)=
      ((2*(a+1)+2:Nat):Int)+(d+1:Int) from by
        simpa only using gp0_Q_phase0 d (a+1) m h,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_Q_phase5 d a m (by omega),
    if_pos (by omega)]

theorem fpar_Q_phase1 (d a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.fpar (Q d m) 0 ((6*a+3:Nat):Int) 0=
      ((6*a+2:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [length_Q]
  rw [show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+3) (Q d m)
    (Trans.Recal.gp0 (Q d m) ((6*a+3:Nat):Int)) ((6*a+2:Nat):Int) 0=_
  rw [gp0_Q_phase1 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase0 d a m (by omega),if_pos (by omega)]

theorem fpar_Q_phase2 (d a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.fpar (Q d m) 0 ((6*a+4:Nat):Int) 0=
      ((6*a+3:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [length_Q]
  rw [show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+3) (Q d m)
    (Trans.Recal.gp0 (Q d m) ((6*a+4:Nat):Int)) ((6*a+3:Nat):Int) 0=_
  rw [gp0_Q_phase2 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase1 d a m (by omega),if_pos (by omega)]

theorem fpar_Q_phase3 (d a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.fpar (Q d m) 0 ((6*a+5:Nat):Int) 0=
      ((6*a+3:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [length_Q]
  rw [show ((6*a+5:Nat):Int)-1=((6*a+4:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+3) (Q d m)
    (Trans.Recal.gp0 (Q d m) ((6*a+5:Nat):Int)) ((6*a+4:Nat):Int) 0=_
  rw [gp0_Q_phase3 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase2 d a m (by omega),if_neg (by omega),
    show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase1 d a m (by omega),if_pos (by omega)]

theorem fpar_Q_phase4 (d a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.fpar (Q d m) 0 ((6*a+6:Nat):Int) 0=
      ((6*a+3:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [length_Q]
  rw [show ((6*a+6:Nat):Int)-1=((6*a+5:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+3) (Q d m)
    (Trans.Recal.gp0 (Q d m) ((6*a+6:Nat):Int)) ((6*a+5:Nat):Int) 0=_
  rw [gp0_Q_phase4 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase3 d a m (by omega),if_neg (by omega),
    show ((6*a+5:Nat):Int)-1=((6*a+4:Nat):Int) by omega]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase2 d a m (by omega),if_neg (by omega),
    show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega),gp0_Q_phase1 d a m (by omega),
    if_pos (by omega)]

theorem fpar_Q_phase5 (d a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.fpar (Q d m) 0 ((6*a+7:Nat):Int) 0=
      ((6*a+2:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),if_pos (by rfl)]
  rw [length_Q]
  rw [show ((6*a+7:Nat):Int)-1=((6*a+6:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+3) (Q d m)
    (Trans.Recal.gp0 (Q d m) ((6*a+7:Nat):Int)) ((6*a+6:Nat):Int) 0=_
  rw [gp0_Q_phase5 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase4 d a m (by omega),if_neg (by omega),
    show ((6*a+6:Nat):Int)-1=((6*a+5:Nat):Int) by omega]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase3 d a m (by omega),if_neg (by omega),
    show ((6*a+5:Nat):Int)-1=((6*a+4:Nat):Int) by omega]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega),gp0_Q_phase2 d a m (by omega),
    if_neg (by omega),show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,
    show m-1+1=m by omega,if_neg (by omega),
    gp0_Q_phase1 d a m (by omega),
    if_neg (by omega),show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  rw [show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_Q_phase0 d a m (by omega),
    if_pos (by omega)]

theorem fpar_Q_tail_pos (d m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (Q d m) 0 ((k+2:Nat):Int) 0=
      ((parentT k+2:Nat):Int) := by
  have hp : k%6=0∨k%6=1∨k%6=2∨k%6=3∨k%6=4∨k%6=5 := by omega
  rcases hp with h0|h1|h2|h3|h4|h5
  · have he : k=6*((k/6-1)+1) := by omega
    rw [he,parentT_phase0]
    simpa only [show 6*((k/6-1)+1)+2=6*((k/6-1)+1)+2 by rfl,
      show 6*(k/6-1)+5+2=6*(k/6-1)+7 by omega] using
      fpar_Q_phase0 d (k/6-1) m (by omega)
  · have he : k=6*(k/6)+1 := by omega
    rw [he,parentT_phase1]
    exact fpar_Q_phase1 d (k/6) m (by omega)
  · have he : k=6*(k/6)+2 := by omega
    rw [he,parentT_phase2]
    exact fpar_Q_phase2 d (k/6) m (by omega)
  · have he : k=6*(k/6)+3 := by omega
    rw [he,parentT_phase3]
    exact fpar_Q_phase3 d (k/6) m (by omega)
  · have he : k=6*(k/6)+4 := by omega
    rw [he,parentT_phase4]
    exact fpar_Q_phase4 d (k/6) m (by omega)
  · have he : k=6*(k/6)+5 := by omega
    rw [he,parentT_phase5]
    exact fpar_Q_phase5 d (k/6) m (by omega)

def parentQ (k : Nat) : Nat :=
  if k=1 then 0 else if k=2 then 1 else parentT (k-2)+2

theorem parentQ_lt (k : Nat) (hk : 0<k) : parentQ k<k := by
  unfold parentQ
  split <;> rename_i h1
  · omega
  split <;> rename_i h2
  · omega
  have hp:=parentT_lt (k-2) (by omega)
  omega

theorem fpar_Q_pos (d m k : Nat) (hk0 : 0<k) (hk : k<m+2) :
    Trans.Recal.fpar (Q d m) 0 (k:Int) 0=(parentQ k:Nat) := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      rw [show parentQ 1=0 by
        unfold parentQ
        rw [if_pos (by rfl)]]
      exact fpar_Q_one d m
    | succ k =>
      by_cases hkz:k=0
      · subst k
        rw [show parentQ 2=1 by
          unfold parentQ
          rw [if_neg (by omega),if_pos (by rfl)]]
        exact fpar_Q_tail_zero d m (by omega)
      · rw [show parentQ (k+2)=parentT k+2 from by
          unfold parentQ
          rw [if_neg (by omega),if_neg (by omega)]
          rw [show k+2-2=k by omega]]
        exact fpar_Q_tail_pos d m k (by omega) (by omega)

theorem isAncAux_Q (d : Nat) (k : Nat) : ∀ m f : Nat, k<m+2 → k<f →
    Trans.Recal.isAncAux f (Q d m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, k<m+2 → k<f →
    Trans.Recal.isAncAux f (Q d m) 0 (k:Int) 0=true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_Q_pos d m k (by omega) hkm]
      rw [show (((parentQ k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hp:=parentQ_lt k (by omega)
      exact ih (parentQ k) hp m f (by omega) (by omega)

theorem isAnc_Q (d m k : Nat) (hk : k<m+2) :
    Trans.Recal.isAnc (Q d m) 0 (k:Int) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),length_Q]
  exact isAncAux_Q d k m (m+3) hk (by omega)

theorem isPrincipalP_Q (d m : Nat) :
    Trans.Recal.isPrincipalP (Q d m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (Q d m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_Q]
    simp]
  simp only [Bool.not_false,Bool.true_and]
  rw [show Trans.Recal.lenI (Q d m)-1=((m+1:Nat):Int) from by
    unfold Trans.Recal.lenI; rw [length_Q]; omega]
  exact isAnc_Q d m (m+1) (by omega)

theorem fpar0_Q_one (d m : Nat) : Trans.Recal.fpar0 (Q d m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),length_Q]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar0_Q_two_lb (d m : Nat) (hm : 0<m) :
    Trans.Recal.fpar0 (Q d m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),length_Q]
  rw [show Trans.Recal.gp0 (Q d m) 2=2+(d+1:Int) from by
    simpa only [p_phase0 0] using gp0_Q_tail d m 0 hm]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (2:Int)-1=1 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (Q d m) 1=2 from rfl,if_pos (by omega)]

theorem fpar0_Q_one_lb (d m : Nat) :
    Trans.Recal.fpar0 (Q d m) 1 1=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega),length_Q]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_Q_one (d m : Nat) :
    Trans.Recal.fpar (Q d m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_Q]
  rw [show Trans.Recal.gp1 (Q d m) 1=1 from rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_Q_one]
  rfl

theorem fpar1_Q_two_lb (d m : Nat) (hm : 0<m) :
    Trans.Recal.fpar (Q d m) 1 2 1=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_Q]
  rw [show Trans.Recal.gp1 (Q d m) 2=0 from by
    simpa only [q_phase0 0] using gp1_Q_tail d m 0 hm]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_Q_two_lb d m hm]
  rw [if_neg (by omega),show Trans.Recal.gp1 (Q d m) 1=1 from rfl,
    if_neg (by omega)]
  rw [fpar0_Q_one_lb,if_pos (by omega)]

theorem trMax_Q (d m : Nat) : Trans.Recal.trMax (Q d m)=1 := by
  cases m with
  | zero => rfl
  | succ m =>
    show Trans.Recal.trMaxAux ((Q d (m+1)).length+1) (Q d (m+1)) 0=1
    rw [length_Q]
    simp only [Trans.Recal.trMaxAux]
    rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega)]
    rw [show Trans.Recal.isParentP (Q d (m+1)) 1 (0+1) 0=true from by
      unfold Trans.Recal.isParentP
      rw [show Trans.Recal.fpar (Q d (m+1)) 1 (0+1) 0=0 from by
        simpa using fpar1_Q_one d (m+1)]
      unfold Trans.Recal.lenI
      rw [length_Q]
      rw [show decide ((0:Int)<((m+3:Nat):Int))=true from
        decide_eq_true (by omega)]
      rfl]
    simp only [Bool.not_true,Bool.false_eq_true,if_false]
    rw [if_neg (by unfold Trans.Recal.lenI; rw [length_Q]; omega)]
    rw [show Trans.Recal.isParentP (Q d (m+1)) 1 (0+1+1) (0+1)=false from by
      unfold Trans.Recal.isParentP
      rw [show Trans.Recal.fpar (Q d (m+1)) 1 (0+1+1) (0+1)=-1 from by
        simpa using fpar1_Q_two_lb d (m+1) (by omega)]
      simp,if_pos (by rfl)]
    omega

theorem drop_two_Q (d m : Nat) : (Q d m).drop 2=TS (d+1) m := rfl

theorem brF_Q (d m : Nat) :
    Trans.Recal.brF (Q d m)=if m=0 then [] else [TS (d+1) m] := by
  unfold Trans.Recal.brF
  rw [trMax_Q]
  change Trans.Recal.ppair ((Q d m).drop 2)=_
  rw [drop_two_Q]
  exact ppair_TS ((d+1:Nat):Int) m

theorem firstNodes_Q (d m : Nat) :
    Trans.Recal.firstNodes (Q d m)=
      if m=0 then [2] else [2,((m+2:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_Q,trMax_Q]
  split <;> rename_i hm
  · simp
  · simp only [List.foldl_cons,List.foldl_nil,length_TS,List.map_cons,List.map_nil]
    simp
    push_cast
    omega

theorem joints_Q (d m : Nat) :
    Trans.Recal.joints (Q d m)=if m=0 then [] else [1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_Q]
  split <;> rename_i hm
  · rfl
  · change [Trans.Recal.fpar (Q d m) 0 2 0]=[1]
    rw [fpar_Q_tail_zero d m (by omega)]

theorem incrFirst_S_two (m : Nat) :
    Trans.Recal.incrFirst (S m) 2=T m := by
  unfold S
  rw [incrFirst_TS]
  rw [show (-2:Int)+2=0 by omega]
  exact incrFirst_zero _

theorem red_Q_zero (d f : Nat) :
    Trans.Recal.red (f+1) (Q d 0)=[(0,0),(1,1)] := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (Q d 0)=false from by
      unfold Trans.Recal.isZeroP; rw [length_Q]; rfl,
    isPrincipalP_Q]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (Q d 0) 0==0 &&
    Trans.Recal.gp1 (Q d 0) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_Q]
  rw [show Trans.Recal.lenI (Q d 0)-1=1 from by
    unfold Trans.Recal.lenI; rw [length_Q]; omega]
  rfl

theorem red_Q_succ_from_N (d m f : Nat)
    (hN : Trans.Recal.red f (N (d+1) (m+1))=S (m+1)) :
    Trans.Recal.red (f+1) (Q d (m+1))=[(0,0)]++V (m+1) := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (Q d (m+1))=false from by
      unfold Trans.Recal.isZeroP; rw [length_Q]; simp,
    isPrincipalP_Q]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (Q d (m+1)) 0==0 &&
    Trans.Recal.gp1 (Q d (m+1)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_Q]
  rw [show Trans.Recal.lenI (Q d (m+1))-1=((m+2:Nat):Int) from by
    unfold Trans.Recal.lenI; rw [length_Q]; omega]
  rw [show ((1:Int)==((m+2:Nat):Int))=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_Q,firstNodes_Q,joints_Q]
  simp only [show ¬m+1=0 by omega,if_false,List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([TS ((d:Int)+1) (m+1)]:List Trans.Recal.PS).getD 0 []=
      TS ((d:Int)+1) (m+1) from rfl,
    show ([2,((m+1+2:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([1]:List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (TS ((d:Int)+1) (m+1)) 0=0 from by
    simpa only [q_phase0 0] using gp1_TS ((d:Int)+1) (m+1) 0 (by omega)]
  simp only [show ((0:Int)==0)=true from rfl,if_true]
  change Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst
    (Trans.Recal.red f ((2,0)::Trans.Recal.derp
      (TS ((d:Int)+1) (m+1)))) 2=[(0,0)]++V (m+1)
  rw [show (d:Int)+1=((d+1:Nat):Int) by omega]
  change Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst
    (Trans.Recal.red f (N (d+1) (m+1))) 2=[(0,0)]++V (m+1)
  rw [hN,incrFirst_S_two]
  rfl

/-! The nonzero-root state `J`. -/

theorem gp0_J_tail (d m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (J d m) ((k+1:Nat):Int)=p k+(d:Int) := by
  show (if ((k+1:Nat):Int)<0 then 0 else
    ((J d m).getD (k+1) (0,0)).1)=_
  rw [if_neg (by omega)]
  change ((TS (d:Int) m).getD k (0,0)).1=_
  have h:=gp0_TS (d:Int) m k hk
  unfold Trans.Recal.gp0 at h
  rw [if_neg (by omega)] at h
  exact h

theorem gp1_J_tail (d m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (J d m) ((k+1:Nat):Int)=q k := by
  show (if ((k+1:Nat):Int)<0 then 0 else
    ((J d m).getD (k+1) (0,0)).2)=_
  rw [if_neg (by omega)]
  change ((TS (d:Int) m).getD k (0,0)).2=_
  have h:=gp1_TS (d:Int) m k hk
  unfold Trans.Recal.gp1 at h
  rw [if_neg (by omega)] at h
  exact h

theorem gp0_J_phase0 (d a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp0 (J d m) ((6*a+1:Nat):Int)=
      ((2*a+2:Nat):Int)+(d:Int) := by
  simpa only [p_phase0 a] using gp0_J_tail d m (6*a) h

theorem gp0_J_phase1 (d a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.gp0 (J d m) ((6*a+2:Nat):Int)=
      ((2*a+3:Nat):Int)+(d:Int) := by
  simpa only [show 6*a+1+1=6*a+2 by omega,p_phase1 a] using
    gp0_J_tail d m (6*a+1) h

theorem gp0_J_phase2 (d a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.gp0 (J d m) ((6*a+3:Nat):Int)=
      ((2*a+4:Nat):Int)+(d:Int) := by
  simpa only [show 6*a+2+1=6*a+3 by omega,p_phase2 a] using
    gp0_J_tail d m (6*a+2) h

theorem gp0_J_phase3 (d a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.gp0 (J d m) ((6*a+4:Nat):Int)=
      ((2*a+4:Nat):Int)+(d:Int) := by
  simpa only [show 6*a+3+1=6*a+4 by omega,p_phase3 a] using
    gp0_J_tail d m (6*a+3) h

theorem gp0_J_phase4 (d a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.gp0 (J d m) ((6*a+5:Nat):Int)=
      ((2*a+4:Nat):Int)+(d:Int) := by
  simpa only [show 6*a+4+1=6*a+5 by omega,p_phase4 a] using
    gp0_J_tail d m (6*a+4) h

theorem gp0_J_phase5 (d a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.gp0 (J d m) ((6*a+6:Nat):Int)=
      ((2*a+3:Nat):Int)+(d:Int) := by
  simpa only [show 6*a+5+1=6*a+6 by omega,p_phase5 a] using
    gp0_J_tail d m (6*a+5) h

theorem fpar_J_tail_zero (d m : Nat) (hm : 0<m) :
    Trans.Recal.fpar (J d m) 0 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),if_pos (by rfl),
    length_J]
  rw [show Trans.Recal.gp0 (J d m) 1=2+(d:Int) from by
    simpa only [p_phase0 0] using gp0_J_tail d m 0 hm]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (J d m) 0=1 from rfl,if_pos (by omega)]

theorem fpar_J_phase0 (d a m : Nat) (h : 6*(a+1)<m) :
    Trans.Recal.fpar (J d m) 0 ((6*(a+1)+1:Nat):Int) 0=
      ((6*a+6:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),if_pos (by rfl),
    length_J]
  rw [show ((6*(a+1)+1:Nat):Int)-1=((6*a+6:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2) (J d m)
    (Trans.Recal.gp0 (J d m) ((6*(a+1)+1:Nat):Int)) ((6*a+6:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (J d m) ((6*(a+1)+1:Nat):Int)=
      ((2*(a+1)+2:Nat):Int)+(d:Int) from by
        simpa only using gp0_J_phase0 d (a+1) m h,
    Trans.Recal.fpar0Aux,if_neg (by omega),gp0_J_phase5 d a m (by omega),
    if_pos (by omega)]

theorem fpar_J_phase1 (d a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.fpar (J d m) 0 ((6*a+2:Nat):Int) 0=((6*a+1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),if_pos (by rfl),
    length_J]
  rw [show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2) (J d m)
    (Trans.Recal.gp0 (J d m) ((6*a+2:Nat):Int)) ((6*a+1:Nat):Int) 0=_
  rw [gp0_J_phase1 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase0 d a m (by omega),if_pos (by omega)]

theorem fpar_J_phase2 (d a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.fpar (J d m) 0 ((6*a+3:Nat):Int) 0=((6*a+2:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),if_pos (by rfl),
    length_J]
  rw [show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2) (J d m)
    (Trans.Recal.gp0 (J d m) ((6*a+3:Nat):Int)) ((6*a+2:Nat):Int) 0=_
  rw [gp0_J_phase2 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase1 d a m (by omega),if_pos (by omega)]

theorem fpar_J_phase3 (d a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.fpar (J d m) 0 ((6*a+4:Nat):Int) 0=((6*a+2:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),if_pos (by rfl),
    length_J]
  rw [show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2) (J d m)
    (Trans.Recal.gp0 (J d m) ((6*a+4:Nat):Int)) ((6*a+3:Nat):Int) 0=_
  rw [gp0_J_phase3 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase2 d a m (by omega),if_neg (by omega),
    show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  rw [show m+1=m+1 by rfl,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase1 d a m (by omega),if_pos (by omega)]

theorem fpar_J_phase4 (d a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.fpar (J d m) 0 ((6*a+5:Nat):Int) 0=((6*a+2:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),if_pos (by rfl),
    length_J]
  rw [show ((6*a+5:Nat):Int)-1=((6*a+4:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2) (J d m)
    (Trans.Recal.gp0 (J d m) ((6*a+5:Nat):Int)) ((6*a+4:Nat):Int) 0=_
  rw [gp0_J_phase4 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase3 d a m (by omega),if_neg (by omega),
    show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  rw [show m+1=m+1 by rfl,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase2 d a m (by omega),if_neg (by omega),
    show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,
    show m-1+1=m by omega,if_neg (by omega),gp0_J_phase1 d a m (by omega),
    if_pos (by omega)]

theorem fpar_J_phase5 (d a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.fpar (J d m) 0 ((6*a+6:Nat):Int) 0=((6*a+1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),if_pos (by rfl),
    length_J]
  rw [show ((6*a+6:Nat):Int)-1=((6*a+5:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+2) (J d m)
    (Trans.Recal.gp0 (J d m) ((6*a+6:Nat):Int)) ((6*a+5:Nat):Int) 0=_
  rw [gp0_J_phase5 d a m h,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase4 d a m (by omega),if_neg (by omega),
    show ((6*a+5:Nat):Int)-1=((6*a+4:Nat):Int) by omega]
  rw [show m+1=m+1 by rfl,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase3 d a m (by omega),if_neg (by omega),
    show ((6*a+4:Nat):Int)-1=((6*a+3:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux,
    show m-1+1=m by omega,if_neg (by omega),gp0_J_phase2 d a m (by omega),
    if_neg (by omega),show ((6*a+3:Nat):Int)-1=((6*a+2:Nat):Int) by omega]
  rw [show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase1 d a m (by omega),if_neg (by omega),
    show ((6*a+2:Nat):Int)-1=((6*a+1:Nat):Int) by omega]
  rw [show m-2=(m-3)+1 by omega,Trans.Recal.fpar0Aux,if_neg (by omega),
    gp0_J_phase0 d a m (by omega),if_pos (by omega)]

theorem fpar_J_tail_pos (d m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (J d m) 0 ((k+1:Nat):Int) 0=
      ((parentT k+1:Nat):Int) := by
  have hp : k%6=0∨k%6=1∨k%6=2∨k%6=3∨k%6=4∨k%6=5 := by omega
  rcases hp with h0|h1|h2|h3|h4|h5
  · have he : k=6*((k/6-1)+1) := by omega
    rw [he,parentT_phase0]
    simpa only [show 6*(k/6-1)+5+1=6*(k/6-1)+6 by omega] using
      fpar_J_phase0 d (k/6-1) m (by omega)
  · have he : k=6*(k/6)+1 := by omega
    rw [he,parentT_phase1]
    exact fpar_J_phase1 d (k/6) m (by omega)
  · have he : k=6*(k/6)+2 := by omega
    rw [he,parentT_phase2]
    exact fpar_J_phase2 d (k/6) m (by omega)
  · have he : k=6*(k/6)+3 := by omega
    rw [he,parentT_phase3]
    exact fpar_J_phase3 d (k/6) m (by omega)
  · have he : k=6*(k/6)+4 := by omega
    rw [he,parentT_phase4]
    exact fpar_J_phase4 d (k/6) m (by omega)
  · have he : k=6*(k/6)+5 := by omega
    rw [he,parentT_phase5]
    exact fpar_J_phase5 d (k/6) m (by omega)

def parentJ (k : Nat) : Nat := if k=1 then 0 else parentT (k-1)+1

theorem parentJ_lt (k : Nat) (hk : 0<k) : parentJ k<k := by
  unfold parentJ
  split <;> rename_i h1
  · omega
  have hp:=parentT_lt (k-1) (by omega)
  omega

theorem fpar_J_pos (d m k : Nat) (hk0 : 0<k) (hk : k<m+1) :
    Trans.Recal.fpar (J d m) 0 (k:Int) 0=(parentJ k:Nat) := by
  cases k with
  | zero => omega
  | succ k =>
    by_cases hkz:k=0
    · subst k
      rw [show parentJ 1=0 by
        unfold parentJ
        rw [if_pos (by rfl)]]
      exact fpar_J_tail_zero d m (by omega)
    · rw [show parentJ (k+1)=parentT k+1 from by
        unfold parentJ
        rw [if_neg (by omega)]
        rw [show k+1-1=k by omega]]
      exact fpar_J_tail_pos d m k (by omega) (by omega)

theorem isAncAux_J (d : Nat) (k : Nat) : ∀ m f : Nat, k<m+1 → k<f →
    Trans.Recal.isAncAux f (J d m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, k<m+1 → k<f →
    Trans.Recal.isAncAux f (J d m) 0 (k:Int) 0=true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_J_pos d m k (by omega) hkm]
      rw [show (((parentJ k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hp:=parentJ_lt k (by omega)
      exact ih (parentJ k) hp m f (by omega) (by omega)

theorem isPrincipalP_J (d m : Nat) :
    Trans.Recal.isPrincipalP (J d m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (J d m)=false from by
    unfold Trans.Recal.isZeroP; rw [length_J]; cases m <;> rfl]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_J]; omega),length_J]
  rw [show Trans.Recal.lenI (J d m)-1=(m:Int) from by
    unfold Trans.Recal.lenI; rw [length_J]; omega]
  exact isAncAux_J d m m (m+2) (by omega) (by omega)

theorem isPrincipalP_V (m : Nat) : Trans.Recal.isPrincipalP (V m)=true := by
  rw [← J_zero_shift]
  exact isPrincipalP_J 0 m

theorem red_J_from_Q (d m f : Nat)
    (hQ : Trans.Recal.red f (Q d m)=[(0,0)]++V m) :
    Trans.Recal.red (f+1) (J d m)=V m := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (J d m)=false from by
      unfold Trans.Recal.isZeroP; rw [length_J]; cases m <;> rfl,
    isPrincipalP_J]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (J d m) 0==0 &&
    Trans.Recal.gp1 (J d m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (J d m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Recal.jjSeq 0 (Trans.Recal.gp1 (J d m) 0-1)++
      Trans.Recal.incrFirst (J d m) (Trans.Recal.gp1 (J d m) 0)=Q d m from by
    rw [show Trans.Recal.gp1 (J d m) 0=1 from rfl]
    exact Q_from_J d m,hQ]
  rw [show Trans.Recal.lenI ([(0,0)]++V m)-1=((m+1:Nat):Int) from by
    unfold Trans.Recal.lenI; rw [List.length_append,List.length_singleton,length_V];
    omega]
  rw [show Trans.Recal.gp1 (J d m) 0=1 from rfl,
    show decide ((1:Int)≤((m+1:Nat):Int))=true from decide_eq_true (by omega)]
  rw [show (([(0,0)]++V m):Trans.Recal.PS).drop (1:Int).toNat=V m from by rfl,
    isPrincipalP_V m]
  simp only [Bool.true_and,if_true]
  rw [show -Trans.Recal.gp0 ([(0,0)]++V m) 1+
      Trans.Recal.gp1 ([(0,0)]++V m) 1=0 from by rfl]
  exact incrFirst_zero _

/-! The zero-row normalization `N → K`. -/

theorem red_N_one (d f : Nat) :
    Trans.Recal.red (f+1) (N (d+1) 1)=S 1 := by
  rw [Trans.Recal.red]
  rfl

theorem red_N_succ_from_K (d m f : Nat)
    (hK : Trans.Recal.red f (K d (m+2))=S (m+2)) :
    Trans.Recal.red (f+1) (N (d+1) (m+2))=S (m+2) := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (N (d+1) (m+2))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_N]
    · rw [show (m+2==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
      rfl
    · omega,
    isPrincipalP_N (d+1) (m+2) (by omega)]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (N (d+1) (m+2)) 0==0 &&
    Trans.Recal.gp1 (N (d+1) (m+2)) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (N (d+1) (m+2)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [show Trans.Recal.gp0 (N (d+1) (m+2)) 0=2 from by rfl]
  rw [K_from_N,hK]

/-! The four branches exposed by a complete block of `K`. -/

def RS (a : Int) (m : Nat) : Trans.Recal.PS :=
  Trans.Recal.incrFirst (R m) a

theorem length_RS (a : Int) (m : Nat) : (RS a m).length=m+4 := by
  simp [RS,Trans.Recal.incrFirst,length_R]

theorem lenI_RS (a : Int) (m : Nat) :
    Trans.Recal.lenI (RS a m)=((m+4:Nat):Int) := by
  unfold Trans.Recal.lenI
  rw [length_RS]

theorem fpar_RS (a : Int) (m j : Nat) (hj : j<m+4) :
    Trans.Recal.fpar (RS a m) 0 (j:Int) 0=
      Trans.Recal.fpar (R m) 0 (j:Int) 0 := by
  unfold RS
  exact Evidence.Cert.fpar_row0_incrFirst (R m) a (j:Int) 0
    (by omega) (by omega) (by rw [lenI_R]; omega)

theorem fAncAux_RS_tail_last (a : Int) (k : Nat) :
    ∀ m f : Nat, ∀ acc : List Int,
    k<m → k+4<f → acc.getLast?=some ((k+4:Nat):Int) →
    (Trans.Recal.fAncAux f (RS a m) 0 ((k+4:Nat):Int) 0 acc).getLast?=
      some 3 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, ∀ acc:List Int,
    k<m → k+4<f → acc.getLast?=some ((k+4:Nat):Int) →
    (Trans.Recal.fAncAux f (RS a m) 0 ((k+4:Nat):Int) 0 acc).getLast?=
      some 3) k ?_
  intro k ih m f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      have hf : Trans.Recal.fpar (RS a m) 0 (((0+4:Nat):Int)) 0=3 := by
        simpa only using (fpar_RS a m 4 (by omega)).trans
          (fpar_R_tail_zero m (by omega))
      rw [hf,if_pos (by omega)]
      cases f with
      | zero => omega
      | succ f =>
        simp only [Trans.Recal.fAncAux]
        rw [show Trans.Recal.fpar (RS a m) 0 3 0=-1 from by
          simpa only using (fpar_RS a m 3 (by omega)).trans (fpar_R_root m),
          if_neg (by omega)]
        simp
    · have hkpos:0<k:=by omega
      rw [fpar_RS a m (k+4) (by omega),
        fpar_R_tail_pos m k hkpos hkm,if_pos (by omega)]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk m f
        (acc++[((parentT k+4:Nat):Int)])
        (by exact Nat.lt_trans hpk hkm) (by omega) (by simp)

theorem fAnc_RS_tail_last (a : Int) (m : Nat) :
    (Trans.Recal.fAnc (RS a m) 0 ((m+3:Nat):Int) 0).getLast?=some 3 := by
  cases m with
  | zero =>
    unfold Trans.Recal.fAnc
    rw [if_neg (by rw [lenI_RS]; omega),length_RS]
    simp only [Trans.Recal.fAncAux]
    have hf : Trans.Recal.fpar (RS a 0) 0 (((0+3:Nat):Int)) 0=-1 := by
      simpa only using (fpar_RS a 0 3 (by omega)).trans (fpar_R_root 0)
    rw [hf,if_neg (by omega)]
    simp
  | succ m =>
    unfold Trans.Recal.fAnc
    rw [if_neg (by rw [lenI_RS]; omega),length_RS]
    have h:=fAncAux_RS_tail_last a ((m+1)-1) (m+1) (m+1+5)
      [(((m+1)-1+4:Nat):Int)] (by omega) (by omega) (by simp)
    simpa only [show (m+1)-1+4=m+1+3 by omega] using h

theorem fAnc_RS_zero (a : Int) (m : Nat) :
    Trans.Recal.fAnc (RS a m) 0 0 0=[0] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_RS]; omega),length_RS]
  simp only [Trans.Recal.fAncAux]
  rw [show Trans.Recal.fpar (RS a m) 0 0 0=-1 from by
    simpa only using (fpar_RS a m 0 (by omega)).trans (fpar_R_zero m),
    if_neg (by omega)]

theorem fAnc_RS_one (a : Int) (m : Nat) :
    Trans.Recal.fAnc (RS a m) 0 1 0=[1] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_RS]; omega),length_RS]
  simp only [Trans.Recal.fAncAux]
  rw [show Trans.Recal.fpar (RS a m) 0 1 0=-1 from by
    simpa only using (fpar_RS a m 1 (by omega)).trans (fpar_R_one m),
    if_neg (by omega)]

theorem fAnc_RS_two (a : Int) (m : Nat) :
    Trans.Recal.fAnc (RS a m) 0 2 0=[2] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_RS]; omega),length_RS]
  simp only [Trans.Recal.fAncAux]
  rw [show Trans.Recal.fpar (RS a m) 0 2 0=-1 from by
    simpa only using (fpar_RS a m 2 (by omega)).trans (fpar_R_two m),
    if_neg (by omega)]

theorem slice_RS_zero (a : Int) (m : Nat) :
    Trans.Recal.slice (RS a m) 0 1=[(2+a,1)] := by
  rfl

theorem slice_RS_one (a : Int) (m : Nat) :
    Trans.Recal.slice (RS a m) 1 2=[(2+a,1)] := by
  rfl

theorem slice_RS_two (a : Int) (m : Nat) :
    Trans.Recal.slice (RS a m) 2 3=[(2+a,0)] := by
  rfl

theorem slice_RS_tail (a : Int) (m : Nat) :
    Trans.Recal.slice (RS a m) 3 ((m+4:Nat):Int)=
      Trans.Recal.incrFirst (V m) a := by
  unfold Trans.Recal.slice RS Trans.Recal.incrFirst
  rw [← List.map_drop,← List.map_take]
  change (((R m).drop 3).take ((((m+4:Nat):Int)-3).toNat)).map
      (fun c => (c.1+a,c.2))=(V m).map (fun c => (c.1+a,c.2))
  rw [show (R m).drop 3=V m from by rfl]
  rw [show ((((m+4:Nat):Int)-3).toNat)=m+1 by omega]
  rw [show (V m).take (m+1)=V m from by
    simpa only [length_V] using (List.take_length (l:=V m))]

theorem ppair_RS (a : Int) (m : Nat) :
    Trans.Recal.ppair (RS a m)=
      [[(2+a,1)],[(2+a,1)],[(2+a,0)],
        Trans.Recal.incrFirst (V m) a] := by
  unfold Trans.Recal.ppair
  rw [length_RS,lenI_RS]
  rw [show m+4+1=m+5 by omega]
  rw [show ((m+4:Nat):Int)-1=((m+3:Nat):Int) by omega]
  rw [show m+5=(m+4)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega)]
  dsimp only
  rw [fAnc_RS_tail_last]
  simp only [Option.getD_some]
  rw [show (3:Int)-1=2 by omega,
    show ((m+3:Nat):Int)+1=((m+4:Nat):Int) by omega,slice_RS_tail]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_RS_two]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (2:Int)-1=1 by omega,show (2:Int)+1=3 by omega,slice_RS_two]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_RS_one]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (1:Int)-1=0 by omega,show (1:Int)+1=2 by omega,slice_RS_one]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_RS_zero]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (0:Int)-1=-1 by omega,show (0:Int)+1=1 by omega,slice_RS_zero]
  rw [Trans.Recal.ppairAux,if_pos (by omega)]

theorem TS_eq_incrFirst_S (e : Int) (m : Nat) :
    TS e m=Trans.Recal.incrFirst (S m) (e+2) := by
  unfold S
  rw [incrFirst_TS]
  rw [show (-2:Int)+(e+2)=e by omega]

theorem drop_two_K_add_six (d m : Nat) :
    (K d (m+6)).drop 2=RS (d+1) m := by
  unfold K Trans.Recal.derp
  simp only [List.singleton_append]
  rw [show List.drop 2 ((0,0)::(TS ((d:Int)-1) (m+6)).drop 1)=
    ((TS ((d:Int)-1) (m+6)).drop 1).drop 1 from by rfl]
  rw [List.drop_drop]
  change (TS ((d:Int)-1) (m+6)).drop 2=RS (d+1) m
  rw [TS_eq_incrFirst_S,S_add_six]
  unfold RS Trans.Recal.incrFirst
  rw [← List.map_drop,drop_two_L]
  apply List.map_congr_left
  intro c _
  apply Prod.ext <;> simp <;> omega

theorem gp0_K_one (d m : Nat) (hm : 1<m) :
    Trans.Recal.gp0 (K d m) 1=(d:Int)+2 := by
  rw [K_eq_A]
  simpa only [show ((6*0+1:Nat):Int)=1 by omega,
    show ((2*0+3:Nat):Int)+((d:Int)-1)=(d:Int)+2 by omega] using
      gp0_A_phase1 0 ((d:Int)-1) 0 m (by omega)

theorem gp1_K_one (d m : Nat) (hm : 1<m) :
    Trans.Recal.gp1 (K d m) 1=1 := by
  rw [K_eq_A]
  simpa only [q] using gp1_A_pos 0 ((d:Int)-1) m 1 (by omega) hm

theorem fpar_K_one (d m : Nat) (hm : 1<m) :
    Trans.Recal.fpar (K d m) 0 1 0=0 := by
  rw [K_eq_A]
  exact fpar_A_phase1_zero 0 ((d:Int)-1) m (by omega) hm

theorem fpar_K_two (d m : Nat) (hm : 2<m) :
    Trans.Recal.fpar (K d m) 0 2 0=1 := by
  rw [K_eq_A]
  simpa only using fpar_A_phase2 0 ((d:Int)-1) 0 m hm

theorem fpar0_K_one (d m : Nat) (hm : 1<m) :
    Trans.Recal.fpar0 (K d m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega),
    length_K d m (by omega)]
  rw [gp0_K_one d m hm]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (K d m) 0=0 from by rfl,if_pos (by omega)]

theorem fpar0_K_two_lb (d m : Nat) (hm : 2<m) :
    Trans.Recal.fpar0 (K d m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega),
    length_K d m (by omega)]
  rw [show Trans.Recal.gp0 (K d m) 2=(d:Int)+3 from by
    rw [K_eq_A]
    simpa only [show ((6*0+2:Nat):Int)=2 by omega,
      show ((2*0+4:Nat):Int)+((d:Int)-1)=(d:Int)+3 by omega] using
        gp0_A_phase2 0 ((d:Int)-1) 0 m (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (2:Int)-1=1 by omega,if_neg (by omega),gp0_K_one d m (by omega),
    if_pos (by omega)]

theorem fpar0_K_one_lb (d m : Nat) (hm : 1<m) :
    Trans.Recal.fpar0 (K d m) 1 1=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega),
    length_K d m (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_K_one (d m : Nat) (hm : 1<m) :
    Trans.Recal.fpar (K d m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_K d m (by omega),gp1_K_one d m hm]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_K_one d m hm]
  rfl

theorem fpar1_K_two_lb (d m : Nat) (hm : 1<m) :
    Trans.Recal.fpar (K d m) 1 2 1=-1 := by
  by_cases hm2 : 2<m
  · unfold Trans.Recal.fpar
    rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
    simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
    rw [length_K d m (by omega)]
    rw [show Trans.Recal.gp1 (K d m) 2=1 from by
      rw [K_eq_A]
      simpa only [q] using gp1_A_pos 0 ((d:Int)-1) m 2 (by omega) hm2]
    simp only [Trans.Recal.fpar1Aux]
    rw [fpar0_K_two_lb d m hm2]
    rw [if_neg (by omega),gp1_K_one d m (by omega),if_neg (by omega)]
    rw [show m=(m-1)+1 by omega,Trans.Recal.fpar1Aux]
    rw [fpar0_K_one_lb d (m-1+1) (by omega),if_pos (by omega)]
  · unfold Trans.Recal.fpar
    rw [if_pos (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]

theorem trMax_K (d m : Nat) (hm : 1<m) : Trans.Recal.trMax (K d m)=1 := by
  show Trans.Recal.trMaxAux ((K d m).length+1) (K d m) 0=1
  rw [length_K d m (by omega)]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by
    unfold Trans.Recal.lenI
    rw [length_K d m (by omega)]
    omega)]
  rw [show Trans.Recal.isParentP (K d m) 1 (0+1) 0=true from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (K d m) 1 (0+1) 0=0 from by
      simpa using fpar1_K_one d m hm]
    unfold Trans.Recal.lenI
    rw [length_K d m (by omega)]
    rw [show decide ((0:Int)<(m:Int))=true from decide_eq_true (by omega)]
    rfl]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [show m=(m-1)+1 by omega,Trans.Recal.trMaxAux]
  rw [if_neg (by
    unfold Trans.Recal.lenI
    rw [length_K d (m-1+1) (by omega)]
    omega)]
  rw [show Trans.Recal.isParentP (K d (m-1+1)) 1 (0+1+1) (0+1)=false from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (K d (m-1+1)) 1 (0+1+1) (0+1)=-1 from by
      simpa using fpar1_K_two_lb d (m-1+1) (by omega)]
    simp,if_pos (by rfl)]
  omega

theorem brF_K_add_six (d m : Nat) :
    Trans.Recal.brF (K d (m+6))=
      [[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
        [(((d+3:Nat):Int),0)],
        Trans.Recal.incrFirst (V m) (d+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_K d (m+6) (by omega)]
  change Trans.Recal.ppair ((K d (m+6)).drop 2)=_
  rw [drop_two_K_add_six,ppair_RS]
  rw [show (2:Int)+((d:Int)+1)=((d+3:Nat):Int) by push_cast; omega]

theorem fpar_K_three (d m : Nat) (hm : 3<m) :
    Trans.Recal.fpar (K d m) 0 3 0=1 := by
  rw [K_eq_A]
  simpa only using fpar_A_phase3 0 ((d:Int)-1) 0 m hm

theorem fpar_K_four (d m : Nat) (hm : 4<m) :
    Trans.Recal.fpar (K d m) 0 4 0=1 := by
  rw [K_eq_A]
  simpa only using fpar_A_phase4 0 ((d:Int)-1) 0 m hm

theorem fpar_K_five (d m : Nat) (hm : 5<m) :
    Trans.Recal.fpar (K d m) 0 5 0=0 := by
  rw [K_eq_A]
  simpa only using fpar_A_phase5 0 ((d:Int)-1) 0 m (by omega) hm

theorem firstNodes_K_add_six (d m : Nat) :
    Trans.Recal.firstNodes (K d (m+6))=
      [2,3,4,5,((m+6:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_K_add_six,trMax_K d (m+6) (by omega)]
  simp only [Trans.Recal.incrFirst,List.foldl_cons,List.foldl_nil,
    List.length_singleton,List.length_map,length_V,List.map_cons,List.map_nil]
  simp
  push_cast
  omega

theorem joints_K_add_six (d m : Nat) :
    Trans.Recal.joints (K d (m+6))=[1,1,1,0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_K_add_six]
  change [Trans.Recal.fpar (K d (m+6)) 0 2 0,
    Trans.Recal.fpar (K d (m+6)) 0 3 0,
    Trans.Recal.fpar (K d (m+6)) 0 4 0,
    Trans.Recal.fpar (K d (m+6)) 0 5 0]=[1,1,1,0]
  rw [fpar_K_two d (m+6) (by omega),fpar_K_three d (m+6) (by omega),
    fpar_K_four d (m+6) (by omega),fpar_K_five d (m+6) (by omega)]

theorem fpar0_K_two (d m : Nat) (hm : 2<m) :
    Trans.Recal.fpar0 (K d m) 2 0=1 := by
  have h:=fpar_K_two d m hm
  unfold Trans.Recal.fpar at h
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega),
    if_pos (by rfl)] at h
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
  exact h

theorem fpar0_K_three (d m : Nat) (hm : 3<m) :
    Trans.Recal.fpar0 (K d m) 3 0=1 := by
  have h:=fpar_K_three d m hm
  unfold Trans.Recal.fpar at h
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega),
    if_pos (by rfl)] at h
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
  exact h

theorem fpar0_K_five (d m : Nat) (hm : 5<m) :
    Trans.Recal.fpar0 (K d m) 5 0=0 := by
  have h:=fpar_K_five d m hm
  unfold Trans.Recal.fpar at h
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega),
    if_pos (by rfl)] at h
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
  exact h

theorem fpar1_K_two (d m : Nat) (hm : 2<m) :
    Trans.Recal.fpar (K d m) 1 2 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_K d m (by omega)]
  rw [show Trans.Recal.gp1 (K d m) 2=1 from by
    rw [K_eq_A]
    simpa only [q] using gp1_A_pos 0 ((d:Int)-1) m 2 (by omega) hm]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_K_two d m hm]
  rw [if_neg (by omega),gp1_K_one d m (by omega),if_neg (by omega)]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar1Aux]
  rw [fpar0_K_one d (m-1+1) (by omega)]
  rw [if_neg (by omega),show Trans.Recal.gp1 (K d (m-1+1)) 0=0 from by rfl,
    if_pos (by omega)]

theorem fpar1_K_three (d m : Nat) (hm : 3<m) :
    Trans.Recal.fpar (K d m) 1 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_K d m (by omega)]
  rw [show Trans.Recal.gp1 (K d m) 3=1 from by
    rw [K_eq_A]
    simpa only [q] using gp1_A_pos 0 ((d:Int)-1) m 3 (by omega) hm]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_K_three d m hm]
  rw [if_neg (by omega),gp1_K_one d m (by omega),if_neg (by omega)]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar1Aux]
  rw [fpar0_K_one d (m-1+1) (by omega)]
  rw [if_neg (by omega),show Trans.Recal.gp1 (K d (m-1+1)) 0=0 from by rfl,
    if_pos (by omega)]

theorem fpar1_K_five (d m : Nat) (hm : 5<m) :
    Trans.Recal.fpar (K d m) 1 5 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_K d m (by omega)]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_K d m (by omega)]
  rw [show Trans.Recal.gp1 (K d m) 5=1 from by
    rw [K_eq_A]
    simpa only [q] using gp1_A_pos 0 ((d:Int)-1) m 5 (by omega) hm]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_K_five d m hm]
  rw [if_neg (by omega),show Trans.Recal.gp1 (K d m) 0=0 from by rfl,
    if_pos (by omega)]

theorem last_NJ_eq_J (d m : Nat) :
    (1,1)::Trans.Recal.derp
      (Trans.Recal.incrFirst (V m) (d+1))=J (d+1) m := by
  unfold V J Trans.Recal.derp Trans.Recal.incrFirst
  simp only [List.map_cons,List.singleton_append]
  rw [show List.drop 1
      ((1+((d:Int)+1),1)::
        (T m).map (fun c => (c.1+((d:Int)+1),c.2)))=
      (T m).map (fun c => (c.1+((d:Int)+1),c.2)) from by rfl]
  unfold TS Trans.Recal.incrFirst
  congr 2

theorem brF_K_two (d : Nat) : Trans.Recal.brF (K d 2)=[] := by
  unfold Trans.Recal.brF
  rw [trMax_K d 2 (by omega)]
  unfold K TS T Trans.Recal.derp Trans.Recal.incrFirst Trans.Recal.ppair
  rfl

theorem drop_K_four (d : Nat) : (K d 4).drop 2=
    [(((d+3:Nat):Int),1),(((d+3:Nat):Int),1)] := by
  unfold K TS T Trans.Recal.derp Trans.Recal.incrFirst p q
  rw [show List.range 4=[0,1,2,3] by rfl]
  simp
  push_cast
  omega

theorem drop_K_five (d : Nat) : (K d 5).drop 2=
    [(((d+3:Nat):Int),1),(((d+3:Nat):Int),1),
      (((d+3:Nat):Int),0)] := by
  unfold K TS T Trans.Recal.derp Trans.Recal.incrFirst p q
  rw [show List.range 5=[0,1,2,3,4] by rfl]
  simp
  push_cast
  omega

theorem fpar_pair_one (x : Int) :
    Trans.Recal.fpar [(x,1),(x,1)] 0 1 0=-1 := by
  have h10 : (1:Int)-1=0 := by omega
  have h0m : (0:Int)-1=-1 := by omega
  have h0lt : ¬((0:Int)<0) := by omega
  have h1lt : ¬((1:Int)<0) := by omega
  have hm1lt : (-1:Int)<0 := by omega
  have hm2lt : (-1:Int)-1<0 := by omega
  have hself : ¬(x<x) := by omega
  unfold Trans.Recal.fpar
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega),if_pos (by rfl)]
  simp only [List.length_cons,List.length_nil,Trans.Recal.fpar0Aux,
    Trans.Recal.gp0,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,
    h10,h0m,h0lt,h1lt,hm1lt,hm2lt,hself,Int.reduceToNat,
    if_false,if_true]

theorem fpar_zero_pair (x : Int) :
    Trans.Recal.fpar [(x,1),(x,1)] 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega),if_pos (by rfl)]
  simp only [List.length_cons,List.length_nil,Trans.Recal.fpar0Aux]
  rfl

theorem fAnc_pair_one (x : Int) :
    Trans.Recal.fAnc [(x,1),(x,1)] 0 1 0=[1] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega)]
  unfold Trans.Recal.fAncAux
  rw [fpar_pair_one,if_neg (by omega)]

theorem fAnc_pair_zero (x : Int) :
    Trans.Recal.fAnc [(x,1),(x,1)] 0 0 0=[0] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega)]
  unfold Trans.Recal.fAncAux
  rw [fpar_zero_pair,if_neg (by omega)]

theorem fpar_triple_two (x : Int) :
    Trans.Recal.fpar [(x,1),(x,1),(x,0)] 0 2 0=-1 := by
  have h21 : (2:Int)-1=1 := by omega
  have h10 : (1:Int)-1=0 := by omega
  have h0m : (0:Int)-1=-1 := by omega
  have h0lt : ¬((0:Int)<0) := by omega
  have h1lt : ¬((1:Int)<0) := by omega
  have h2lt : ¬((2:Int)<0) := by omega
  have hm1lt : (-1:Int)<0 := by omega
  have hself : ¬(x<x) := by omega
  unfold Trans.Recal.fpar
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega),if_pos (by rfl)]
  simp only [List.length_cons,List.length_nil,Trans.Recal.fpar0Aux,
    Trans.Recal.gp0,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,
    h21,h10,h0m,h0lt,h1lt,h2lt,hm1lt,hself,Int.reduceToNat,
    if_false,if_true]

theorem fpar_triple_one (x : Int) :
    Trans.Recal.fpar [(x,1),(x,1),(x,0)] 0 1 0=-1 := by
  have h10 : (1:Int)-1=0 := by omega
  have h0m : (0:Int)-1=-1 := by omega
  have h0lt : ¬((0:Int)<0) := by omega
  have h1lt : ¬((1:Int)<0) := by omega
  have hm1lt : (-1:Int)<0 := by omega
  have hself : ¬(x<x) := by omega
  unfold Trans.Recal.fpar
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega),if_pos (by rfl)]
  simp only [List.length_cons,List.length_nil,Trans.Recal.fpar0Aux,
    Trans.Recal.gp0,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,
    h10,h0m,h0lt,h1lt,hm1lt,hself,Int.reduceToNat,
    if_false,if_true]

theorem fpar_triple_zero (x : Int) :
    Trans.Recal.fpar [(x,1),(x,1),(x,0)] 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega),if_pos (by rfl)]
  simp only [List.length_cons,List.length_nil,Trans.Recal.fpar0Aux]
  rfl

theorem fAnc_triple_two (x : Int) :
    Trans.Recal.fAnc [(x,1),(x,1),(x,0)] 0 2 0=[2] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega)]
  unfold Trans.Recal.fAncAux
  rw [fpar_triple_two,if_neg (by omega)]

theorem fAnc_triple_one (x : Int) :
    Trans.Recal.fAnc [(x,1),(x,1),(x,0)] 0 1 0=[1] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega)]
  unfold Trans.Recal.fAncAux
  rw [fpar_triple_one,if_neg (by omega)]

theorem fAnc_triple_zero (x : Int) :
    Trans.Recal.fAnc [(x,1),(x,1),(x,0)] 0 0 0=[0] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by
    unfold Trans.Recal.lenI
    simp only [List.length_cons,List.length_nil]
    omega)]
  unfold Trans.Recal.fAncAux
  rw [fpar_triple_zero,if_neg (by omega)]

theorem brF_K_three (d : Nat) :
    Trans.Recal.brF (K d 3)=[[(((d+3:Nat):Int),1)]] := by
  unfold Trans.Recal.brF
  rw [trMax_K d 3 (by omega)]
  change Trans.Recal.ppair ((K d 3).drop 2)=_
  rw [show (K d 3).drop 2=[(((d+3:Nat):Int),1)] from by
    unfold K TS T Trans.Recal.derp Trans.Recal.incrFirst p q
    rw [show List.range 3=[0,1,2] by rfl]
    simp
    push_cast
    omega]
  rfl

theorem brF_K_four (d : Nat) :
    Trans.Recal.brF (K d 4)=
      [[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)]] := by
  unfold Trans.Recal.brF
  rw [trMax_K d 4 (by omega)]
  change Trans.Recal.ppair ((K d 4).drop 2)=_
  rw [drop_K_four]
  rw [Trans.Recal.ppair]
  change Trans.Recal.ppairAux 3
    [(((d+3:Nat):Int),1),(((d+3:Nat):Int),1)] 1 []=_
  rw [Trans.Recal.ppairAux,if_neg (by omega),fAnc_pair_one]
  change Trans.Recal.ppairAux 2
    [(((d+3:Nat):Int),1),(((d+3:Nat):Int),1)] 0
      [[(((d+3:Nat):Int),1)]]=_
  rw [Trans.Recal.ppairAux,if_neg (by omega),fAnc_pair_zero]
  rfl

theorem brF_K_five (d : Nat) :
    Trans.Recal.brF (K d 5)=
      [[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
        [(((d+3:Nat):Int),0)]] := by
  unfold Trans.Recal.brF
  rw [trMax_K d 5 (by omega)]
  change Trans.Recal.ppair ((K d 5).drop 2)=_
  rw [drop_K_five]
  rw [Trans.Recal.ppair]
  change Trans.Recal.ppairAux 4
    [(((d+3:Nat):Int),1),(((d+3:Nat):Int),1),(((d+3:Nat):Int),0)] 2 []=_
  rw [Trans.Recal.ppairAux,if_neg (by omega),fAnc_triple_two]
  change Trans.Recal.ppairAux 3
    [(((d+3:Nat):Int),1),(((d+3:Nat):Int),1),(((d+3:Nat):Int),0)] 1
      [[(((d+3:Nat):Int),0)]]=_
  rw [Trans.Recal.ppairAux,if_neg (by omega),fAnc_triple_one]
  change Trans.Recal.ppairAux 2
    [(((d+3:Nat):Int),1),(((d+3:Nat):Int),1),(((d+3:Nat):Int),0)] 0
      [[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),0)]]=_
  rw [Trans.Recal.ppairAux,if_neg (by omega),fAnc_triple_zero]
  rfl

theorem firstNodes_K_two (d : Nat) :
    Trans.Recal.firstNodes (K d 2)=[2] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_K_two,trMax_K d 2 (by omega)]
  rfl

theorem firstNodes_K_three (d : Nat) :
    Trans.Recal.firstNodes (K d 3)=[2,3] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_K_three,trMax_K d 3 (by omega)]
  rfl

theorem firstNodes_K_four (d : Nat) :
    Trans.Recal.firstNodes (K d 4)=[2,3,4] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_K_four,trMax_K d 4 (by omega)]
  rfl

theorem firstNodes_K_five (d : Nat) :
    Trans.Recal.firstNodes (K d 5)=[2,3,4,5] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_K_five,trMax_K d 5 (by omega)]
  rfl

theorem joints_K_two (d : Nat) : Trans.Recal.joints (K d 2)=[] := by
  unfold Trans.Recal.joints
  rw [firstNodes_K_two]
  rfl

theorem joints_K_three (d : Nat) : Trans.Recal.joints (K d 3)=[1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_K_three]
  change [Trans.Recal.fpar (K d 3) 0 2 0]=[1]
  rw [fpar_K_two d 3 (by omega)]

theorem joints_K_four (d : Nat) : Trans.Recal.joints (K d 4)=[1,1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_K_four]
  change [Trans.Recal.fpar (K d 4) 0 2 0,
    Trans.Recal.fpar (K d 4) 0 3 0]=[1,1]
  rw [fpar_K_two d 4 (by omega),fpar_K_three d 4 (by omega)]

theorem joints_K_five (d : Nat) : Trans.Recal.joints (K d 5)=[1,1,1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_K_five]
  change [Trans.Recal.fpar (K d 5) 0 2 0,
    Trans.Recal.fpar (K d 5) 0 3 0,
    Trans.Recal.fpar (K d 5) 0 4 0]=[1,1,1]
  rw [fpar_K_two d 5 (by omega),fpar_K_three d 5 (by omega),
    fpar_K_four d 5 (by omega)]

theorem red_K_one (d f : Nat) :
    Trans.Recal.red (f+3) (K d 1)=S 1 := by
  rfl

theorem red_K_two (d f : Nat) :
    Trans.Recal.red (f+3) (K d 2)=S 2 := by
  rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d 2)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K d 2 (by omega)]
    rfl,isPrincipalP_K d 2 (by omega)]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K d 2) 0==0 &&
    Trans.Recal.gp1 (K d 2) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_K d 2 (by omega)]
  rw [show Trans.Recal.lenI (K d 2)-1=1 from by
    unfold Trans.Recal.lenI
    rw [length_K d 2 (by omega)]
    omega]
  rw [show ((1:Int)==1)=true from rfl]
  rw [S_two]
  rfl

theorem red_K_three (d f : Nat) :
    Trans.Recal.red (f+3) (K d 3)=S 3 := by
  rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d 3)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K d 3 (by omega)]
    rfl,isPrincipalP_K d 3 (by omega)]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K d 3) 0==0 &&
    Trans.Recal.gp1 (K d 3) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_K d 3 (by omega)]
  rw [show Trans.Recal.lenI (K d 3)-1=2 from by
    unfold Trans.Recal.lenI
    rw [length_K d 3 (by omega)]
    omega]
  simp only [show ((1:Int)==2)=false from rfl,Bool.false_eq_true,if_false]
  rw [brF_K_three,firstNodes_K_three,joints_K_three]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(((d+3:Nat):Int),1)]]:List Trans.Recal.PS).getD 0 []=
      [(((d+3:Nat):Int),1)] from rfl,
    show ([2,3]:List Int).getD 0 0=2 from rfl,
    show ([1]:List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 [(((d+3:Nat):Int),1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_K_two d 3 (by omega)]
  change Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red (f+2) [(2,1)]) 1=S 3
  have hx : Trans.Recal.red (f+2) [(2,1)]=[(1,1)] := G1.red_X1 f
  rw [hx,S_three]
  rfl

theorem red_K_four (d f : Nat) :
    Trans.Recal.red (f+3) (K d 4)=S 4 := by
  rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d 4)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K d 4 (by omega)]
    rfl,isPrincipalP_K d 4 (by omega)]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K d 4) 0==0 &&
    Trans.Recal.gp1 (K d 4) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_K d 4 (by omega)]
  rw [show Trans.Recal.lenI (K d 4)-1=3 from by
    unfold Trans.Recal.lenI
    rw [length_K d 4 (by omega)]
    omega]
  simp only [show ((1:Int)==3)=false from rfl,Bool.false_eq_true,if_false]
  rw [brF_K_four,firstNodes_K_four,joints_K_four]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 2=[0,1] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)]]:
      List Trans.Recal.PS).getD 0 []=[(((d+3:Nat):Int),1)] from rfl,
    show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)]]:
      List Trans.Recal.PS).getD 1 []=[(((d+3:Nat):Int),1)] from rfl,
    show ([2,3,4]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4]:List Int).getD 1 0=3 from rfl,
    show ([1,1]:List Int).getD 0 0=1 from rfl,
    show ([1,1]:List Int).getD 1 0=1 from rfl]
  rw [show Trans.Recal.gp1 [(((d+3:Nat):Int),1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_K_two d 4 (by omega),fpar1_K_three d 4 (by omega)]
  change (Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red (f+2) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+2) [(2,1)]) 1=S 4
  have hx : Trans.Recal.red (f+2) [(2,1)]=[(1,1)] := G1.red_X1 f
  rw [hx,S_four]
  rfl

theorem red_K_five (d f : Nat) :
    Trans.Recal.red (f+3) (K d 5)=S 5 := by
  rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d 5)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K d 5 (by omega)]
    rfl,isPrincipalP_K d 5 (by omega)]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K d 5) 0==0 &&
    Trans.Recal.gp1 (K d 5) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_K d 5 (by omega)]
  rw [show Trans.Recal.lenI (K d 5)-1=4 from by
    unfold Trans.Recal.lenI
    rw [length_K d 5 (by omega)]
    omega]
  simp only [show ((1:Int)==4)=false from rfl,Bool.false_eq_true,if_false]
  rw [brF_K_five,firstNodes_K_five,joints_K_five]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 3=[0,1,2] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
      [(((d+3:Nat):Int),0)]]:List Trans.Recal.PS).getD 0 []=
        [(((d+3:Nat):Int),1)] from rfl,
    show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
      [(((d+3:Nat):Int),0)]]:List Trans.Recal.PS).getD 1 []=
        [(((d+3:Nat):Int),1)] from rfl,
    show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
      [(((d+3:Nat):Int),0)]]:List Trans.Recal.PS).getD 2 []=
        [(((d+3:Nat):Int),0)] from rfl,
    show ([2,3,4,5]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4,5]:List Int).getD 1 0=3 from rfl,
    show ([2,3,4,5]:List Int).getD 2 0=4 from rfl,
    show ([1,1,1]:List Int).getD 0 0=1 from rfl,
    show ([1,1,1]:List Int).getD 1 0=1 from rfl,
    show ([1,1,1]:List Int).getD 2 0=1 from rfl]
  rw [show Trans.Recal.gp1 [(((d+3:Nat):Int),1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_K_two d 5 (by omega),fpar1_K_three d 5 (by omega)]
  rw [show Trans.Recal.gp1 [(((d+3:Nat):Int),0)] 0=0 from rfl,
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  change ((Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red (f+2) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+2) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+2) [(2,0)]) 2=S 5
  have hx : Trans.Recal.red (f+2) [(2,1)]=[(1,1)] := G1.red_X1 f
  have hz : Trans.Recal.red (f+2) [(2,0)]=[(0,0)] := by
    simpa only [show f+2=(f+1)+1 by omega] using G9.red_single_zero (f+1)
  rw [hx,hz,S_five]
  rfl

theorem red_K_add_six_from_J (d m f : Nat)
    (hJ : Trans.Recal.red (f+2) (J (d+1) m)=V m) :
    Trans.Recal.red (f+3) (K d (m+6))=S (m+6) := by
  rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K d (m+6))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K d (m+6) (by omega)]
    rw [show (m+6==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
    rfl,
    isPrincipalP_K d (m+6) (by omega)]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K d (m+6)) 0==0 &&
    Trans.Recal.gp1 (K d (m+6)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_K d (m+6) (by omega)]
  rw [show Trans.Recal.lenI (K d (m+6))-1=((m+5:Nat):Int) from by
    unfold Trans.Recal.lenI
    rw [length_K d (m+6) (by omega)]
    omega]
  rw [show ((1:Int)==((m+5:Nat):Int))=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_K_add_six,firstNodes_K_add_six,joints_K_add_six]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 4=[0,1,2,3] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
      [(((d+3:Nat):Int),0)],Trans.Recal.incrFirst (V m) (d+1)] :
      List Trans.Recal.PS).getD 0 []=[(((d+3:Nat):Int),1)] from rfl,
    show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
      [(((d+3:Nat):Int),0)],Trans.Recal.incrFirst (V m) (d+1)] :
      List Trans.Recal.PS).getD 1 []=[(((d+3:Nat):Int),1)] from rfl,
    show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
      [(((d+3:Nat):Int),0)],Trans.Recal.incrFirst (V m) (d+1)] :
      List Trans.Recal.PS).getD 2 []=[(((d+3:Nat):Int),0)] from rfl,
    show ([[(((d+3:Nat):Int),1)],[(((d+3:Nat):Int),1)],
      [(((d+3:Nat):Int),0)],Trans.Recal.incrFirst (V m) (d+1)] :
      List Trans.Recal.PS).getD 3 []=
        Trans.Recal.incrFirst (V m) (d+1) from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 1 0=3 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 2 0=4 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 3 0=5 from rfl,
    show ([1,1,1,0]:List Int).getD 0 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 1 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 2 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 3 0=0 from rfl]
  rw [show Trans.Recal.gp1 [(((d+3:Nat):Int),1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_K_two d (m+6) (by omega)]
  rw [show Trans.Recal.gp1 [(((d+3:Nat):Int),0)] 0=0 from rfl,
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [fpar1_K_three d (m+6) (by omega)]
  rw [show Trans.Recal.gp1
      (Trans.Recal.incrFirst (V m) (d+1)) 0=1 from by
    unfold V Trans.Recal.incrFirst
    rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_K_five d (m+6) (by omega)]
  have h21 : ((1+1,0+1)::Trans.Recal.derp [(((d+3:Nat):Int),1)])=
      ([(2,1)]:Trans.Recal.PS) := by rfl
  have h20 : ((1+1,-1+1)::Trans.Recal.derp [(((d+3:Nat):Int),0)])=
      ([(2,0)]:Trans.Recal.PS) := by rfl
  have hlast : ((0+1,0+1)::Trans.Recal.derp
      (Trans.Recal.incrFirst (V m) (d+1)))=J (d+1) m := by
    exact last_NJ_eq_J d m
  rw [h21,h20,hlast]
  have hx : Trans.Recal.red (f+2) [(2,1)]=[(1,1)] := by
    exact G1.red_X1 f
  have hz : Trans.Recal.red (f+2) [(2,0)]=[(0,0)] := by
    simpa only [show f+2=(f+1)+1 by omega] using G9.red_single_zero (f+1)
  rw [hx,hz,hJ]
  rw [show (1:Int)-0=1 by omega,show (1:Int)-(-1)=2 by omega,
    show (0:Int)-0=0 by omega]
  rw [incrFirst_zero,S_add_six]
  rfl

theorem red_six_phase_cycle (m : Nat) :
    (∀ d f : Nat, 0<m →
      Trans.Recal.red (4*m+f+3) (K d m)=S m) ∧
    (∀ d f : Nat, 0<m →
      Trans.Recal.red (4*m+f+4) (N (d+1) m)=S m) ∧
    (∀ d f : Nat,
      Trans.Recal.red (4*m+f+5) (Q d m)=[(0,0)]++V m) ∧
    (∀ d f : Nat,
      Trans.Recal.red (4*m+f+6) (J d m)=V m) := by
  refine Nat.strongRecOn m ?_
  intro m ih
  have hK : ∀ d f : Nat, 0<m →
      Trans.Recal.red (4*m+f+3) (K d m)=S m := by
    intro d f hm
    by_cases hs : m<6
    · have hc : m=1∨m=2∨m=3∨m=4∨m=5 := by omega
      rcases hc with h1|h2|h3|h4|h5
      · subst m
        simpa only [show 4*1+f+3=(f+4)+3 by omega] using red_K_one d (f+4)
      · subst m
        simpa only [show 4*2+f+3=(f+8)+3 by omega] using red_K_two d (f+8)
      · subst m
        simpa only [show 4*3+f+3=(f+12)+3 by omega] using red_K_three d (f+12)
      · subst m
        simpa only [show 4*4+f+3=(f+16)+3 by omega] using red_K_four d (f+16)
      · subst m
        simpa only [show 4*5+f+3=(f+20)+3 by omega] using red_K_five d (f+20)
    · obtain ⟨r,rfl⟩ : ∃ r,m=r+6 := ⟨m-6,by omega⟩
      have hJ0 := (ih r (by omega)).2.2.2 (d+1) (f+20)
      have hJ : Trans.Recal.red ((4*r+f+24)+2) (J (d+1) r)=V r := by
        rw [show (4*r+f+24)+2=4*r+(f+20)+6 by omega]
        exact hJ0
      have hstep := red_K_add_six_from_J d r (4*r+f+24) hJ
      rw [show (4*r+f+24)+3=4*(r+6)+f+3 by omega] at hstep
      exact hstep
  have hN : ∀ d f : Nat, 0<m →
      Trans.Recal.red (4*m+f+4) (N (d+1) m)=S m := by
    intro d f hm
    by_cases h1 : m=1
    · subst m
      simpa only [show 4*1+f+4=(f+7)+1 by omega] using red_N_one d (f+7)
    · obtain ⟨r,rfl⟩ : ∃ r,m=r+2 := ⟨m-2,by omega⟩
      apply red_N_succ_from_K d r (4*(r+2)+f+3)
      exact hK d f (by omega)
  have hQ : ∀ d f : Nat,
      Trans.Recal.red (4*m+f+5) (Q d m)=[(0,0)]++V m := by
    intro d f
    cases m with
    | zero =>
      simpa only [show 4*0+f+5=(f+4)+1 by omega] using red_Q_zero d (f+4)
    | succ r =>
      apply red_Q_succ_from_N d r (4*(r+1)+f+4)
      exact hN d f (by omega)
  have hJ : ∀ d f : Nat,
      Trans.Recal.red (4*m+f+6) (J d m)=V m := by
    intro d f
    apply red_J_from_Q d m (4*m+f+5)
    exact hQ d f
  exact ⟨hK,hN,hQ,hJ⟩

theorem red_V (m f : Nat) :
    Trans.Recal.red (4*m+f+6) (V m)=V m := by
  simpa only [J_zero_shift] using (red_six_phase_cycle m).2.2.2 0 f

theorem fpar0_L_five (m : Nat) :
    Trans.Recal.fpar0 (L m) 5 0=0 := by
  have h:=fpar_L_base_five m
  unfold Trans.Recal.fpar at h
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl)] at h
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega)]
  exact h

theorem fpar1_L_five (m : Nat) :
    Trans.Recal.fpar (L m) 1 5 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  rw [show Trans.Recal.gp1 (L m) 5=1 from by rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_five]
  rw [if_neg (by omega),show Trans.Recal.gp1 (L m) 0=0 from by rfl,
    if_pos (by omega)]

theorem last_L_branch_eq_V (m : Nat) :
    (1,1)::Trans.Recal.derp (V m)=V m := by
  unfold V Trans.Recal.derp
  rfl

theorem red_L_from_V (m f : Nat)
    (hV : Trans.Recal.red (f+2) (V m)=V m) :
    Trans.Recal.red (f+3) (L m)=L m := by
  rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L m)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp,
    isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L m) 0==0 &&
      Trans.Recal.gp1 (L m) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L]
  rw [show Trans.Recal.lenI (L m)-1=((m+5:Nat):Int) from by
    rw [lenI_L]
    omega]
  rw [show ((1:Int)==((m+5:Nat):Int))=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L,firstNodes_L,joints_L]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 4=[0,1,2,3] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(2,1)],[(2,1)],[(2,0)],V m]:
      List Trans.Recal.PS).getD 0 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],V m]:
      List Trans.Recal.PS).getD 1 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],V m]:
      List Trans.Recal.PS).getD 2 []=[(2,0)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],V m]:
      List Trans.Recal.PS).getD 3 []=V m from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 1 0=3 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 2 0=4 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 3 0=5 from rfl,
    show ([1,1,1,0]:List Int).getD 0 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 1 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 2 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 3 0=0 from rfl]
  rw [show Trans.Recal.gp1 [(2,1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_L_two]
  rw [show Trans.Recal.gp1 [(2,0)] 0=0 from rfl,
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [fpar1_L_three]
  rw [show Trans.Recal.gp1 (V m) 0=1 from by rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_L_five]
  have h21 : ((1+1,0+1)::Trans.Recal.derp [(2,1)])=
      ([(2,1)]:Trans.Recal.PS) := by rfl
  have h20 : ((1+1,-1+1)::Trans.Recal.derp [(2,0)])=
      ([(2,0)]:Trans.Recal.PS) := by rfl
  have hlast : ((0+1,0+1)::Trans.Recal.derp (V m))=V m := by
    exact last_L_branch_eq_V m
  rw [h21,h20,hlast]
  have hx : Trans.Recal.red (f+2) [(2,1)]=[(1,1)] := G1.red_X1 f
  have hz : Trans.Recal.red (f+2) [(2,0)]=[(0,0)] := by
    simpa only [show f+2=(f+1)+1 by omega] using G9.red_single_zero (f+1)
  rw [hx,hz,hV]
  rw [show (1:Int)-0=1 by omega,show (1:Int)-(-1)=2 by omega,
    show (0:Int)-0=0 by omega,incrFirst_zero]
  rfl

theorem red_L_bound (m f : Nat) :
    Trans.Recal.red (4*m+f+9) (L m)=L m := by
  apply red_L_from_V m (4*m+f+6)
  rw [show (4*m+f+6)+2=4*m+(f+2)+6 by omega]
  exact red_V m (f+2)

theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  unfold Trans.Recal.redP
  have hf : 4*m+9≤Trans.Recal.redFuel (L m) := by
    unfold Trans.Recal.redFuel
    rw [length_L]
    omega
  obtain ⟨f,hf'⟩ : ∃ f,Trans.Recal.redFuel (L m)=4*m+f+9 :=
    ⟨Trans.Recal.redFuel (L m)-(4*m+9),by omega⟩
  rw [hf']
  exact red_L_bound m f

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  exact G1.beq_PS_self _

/-
The G9 reduction/reader tail copied during the initial six-phase port is kept
temporarily below while the genuinely new six-phase reduction is developed.

def S (m : Nat) : Trans.Recal.PS := Trans.Recal.incrFirst (T m) (-1)

theorem p_add_five (k : Nat) : p (k+5)=p k+1 := by
  unfold p
  rw [show (k+5)%5=k%5 by omega,show (k+5)/5=k/5+1 by omega]
  split <;> rename_i h0
  · push_cast
    omega
  split <;> push_cast <;> omega

theorem q_add_five (k : Nat) : q (k+5)=q k := by
  unfold q
  rw [show (k+5)%5=k%5 by omega]

theorem S_succ (m : Nat) : S (m+1)=S m++[(p m-1,q m)] := by
  unfold S Trans.Recal.incrFirst
  rw [T_succ,List.map_append]
  rfl

theorem S_zero : S 0=[] := rfl
theorem S_one : S 1=Trans.Recal.zeroPS := rfl
theorem S_two : S 2=G1.LG 0 := rfl
theorem S_three : S 3=G1.LG 1 := rfl
theorem S_four : S 4=G1.LG 2 := rfl

theorem S_add_five : ∀ m : Nat, S (m+5)=L m
  | 0 => rfl
  | m+1 => by
    rw [show m+1+5=(m+5)+1 by omega,S_succ,S_add_five m,L_succ]
    congr 1
    apply congrArg (fun x => [x])
    apply Prod.ext
    · rw [p_add_five]
      omega
    · exact q_add_five m

theorem red_LG (m f : Nat) :
    Trans.Recal.red (f+3) (G1.LG m)=G1.LG m := by
  cases m with
  | zero =>
    simpa only [show f+3=(f+2)+1 by omega] using G8.red_A_zero_two (f+2)
  | succ m =>
    rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
    rw [show Trans.Recal.isZeroP (G1.LG (m+1))=false from by
          unfold Trans.Recal.isZeroP
          rw [G1.len_LG]
          simp,
      G1.isPrincipalP_LG]
    simp only [Bool.false_eq_true,if_false,if_true]
    rw [show (Trans.Recal.gp0 (G1.LG (m+1)) 0==0 &&
        Trans.Recal.gp1 (G1.LG (m+1)) 0==0)=true from by rfl]
    simp only [if_true,G1.trMax_LG,G1.lenI_LG]
    rw [show ((1:Int)==(((m+1:Nat):Int)+2-1))=false from
      beq_eq_false_iff_ne.mpr (by omega)]
    simp only [Bool.false_eq_true,if_false,G1.brF_LG,G1.firstNodes_LG,
      G1.joints_LG,List.length_replicate]
    rw [show ((List.range (m+1)).foldl
        (init:=Trans.Recal.jjSeq 0 1)
        (fun (r:Trans.Recal.PS) (J:Nat) =>
          let bJ:=(List.replicate (m+1) [G1.CC]).getD J []
          let nJ:Int:=if Trans.Recal.gp1 bJ 0==0 then -1 else
            Trans.Recal.fpar (G1.LG (m+1)) 1
              (((List.range (m+2)).map fun k:Nat=>(k:Int)+2).getD J 0) 0
          let jnJ:=(List.replicate (m+1) (1:Int)).getD J 0
          let NJ:Trans.Recal.PS:=(jnJ+1,nJ+1)::Trans.Recal.derp bJ
          r++Trans.Recal.incrFirst (Trans.Recal.red (f+2) NJ) (jnJ-nJ)))=
        (List.range (m+1)).foldl (fun r (_:Nat)=>r++[G1.CC])
          (Trans.Recal.jjSeq 0 1) from by
      refine G1.foldl_congr_mem _ _ _ _ (fun J hJ r=>?_)
      have hJ':J<m+1:=List.mem_range.mp hJ
      rw [G1.getD_repl (m+1) J [G1.CC] [] hJ',
        G1.getD_repl (m+1) J (1:Int) 0 hJ',
        G1.getD_map_range (m+2) J (fun k:Nat=>(k:Int)+2) (by omega)]
      dsimp only
      rw [show (Trans.Recal.gp1 [G1.CC] 0==0)=false from rfl]
      simp only [Bool.false_eq_true,if_false]
      rw [G1.fpar_LG_1_e (m+1) ((J:Int)+2) (by omega) (by push_cast; omega)]
      change r++Trans.Recal.incrFirst (Trans.Recal.red (f+2) G1.X1) 1=_
      rw [G1.red_X1 f]
      rfl]
    rw [show Trans.Recal.jjSeq 0 1=[((0:Int),(0:Int)),((1:Int),(1:Int))] from rfl,
      G1.foldStep (m+1)]

theorem red_single_zero (f : Nat) :
    Trans.Recal.red (f+1) [(2,0)]=[(0,0)] := by rfl

theorem isPrincipalP_T (m : Nat) (hm : 2≤m) :
    Trans.Recal.isPrincipalP (T m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (T m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_T]
    rw [show (m==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
    rfl]
  simp only [Bool.not_false,Bool.true_and]
  rw [show Trans.Recal.lenI (T m)-1=((m-1:Nat):Int) from by rw [lenI_T]; omega]
  exact isAnc_T m (m-1) (by omega)

theorem red_L_zero (f : Nat) : Trans.Recal.red (f+4) (L 0)=L 0 := by
  rw [show f+4=(f+3)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L 0)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp,
    isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L 0) 0==0 &&
      Trans.Recal.gp1 (L 0) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L]
  rw [show Trans.Recal.lenI (L 0)-1=4 from by rw [lenI_L]; omega]
  rw [show ((1:Int)==4)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L_zero,firstNodes_L_zero,joints_L_zero]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 3=[0,1,2] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(2,1)],[(2,1)],[(2,0)]]:List Trans.Recal.PS).getD 0 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)]]:List Trans.Recal.PS).getD 1 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)]]:List Trans.Recal.PS).getD 2 []=[(2,0)] from rfl,
    show ([2,3,4,5]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4,5]:List Int).getD 1 0=3 from rfl,
    show ([2,3,4,5]:List Int).getD 2 0=4 from rfl,
    show ([1,1,1]:List Int).getD 0 0=1 from rfl,
    show ([1,1,1]:List Int).getD 1 0=1 from rfl,
    show ([1,1,1]:List Int).getD 2 0=1 from rfl]
  rw [show Trans.Recal.gp1 [(2,1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_L_two]
  rw [show Trans.Recal.gp1 [(2,0)] 0=0 from rfl,
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [fpar1_L_three]
  change ((Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,0)]) 2=L 0
  have hx : Trans.Recal.red (f+3) [(2,1)]=[(1,1)] := by
    change Trans.Recal.red (f+3) G1.X1=[(1,1)]
    simpa only [show f+3=(f+1)+2 by omega] using G1.red_X1 (f+1)
  have hz : Trans.Recal.red (f+3) [(2,0)]=[(0,0)] := by
    simpa only [show f+3=(f+2)+1 by omega] using red_single_zero (f+2)
  rw [hx,hz]
  rfl

theorem T_head (m : Nat) :
    T (m+1)=(1,0)::((List.range m).map fun k=>(p (k+1),q (k+1))) := by
  unfold T
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  rfl

theorem cons_derp_T (m : Nat) :
    (1,0)::Trans.Recal.derp (T (m+1))=T (m+1) := by
  rw [T_head]
  rfl

theorem incrFirst_S (m : Nat) : Trans.Recal.incrFirst (S m) 1=T m := by
  unfold S Trans.Recal.incrFirst T
  rw [List.map_map,List.map_map]
  apply List.map_congr_left
  intro k _
  change (p k+(-1)+1,q k)=(p k,q k)
  apply Prod.ext
  · omega
  · rfl

theorem red_T_one (f : Nat) : Trans.Recal.red (f+1) (T 1)=S 1 := by rfl

theorem red_T_step (m f : Nat) (hm : 2≤m)
    (hred : Trans.Recal.red f (S m)=S m) :
    Trans.Recal.red (f+1) (T m)=S m := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (T m)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_T]
      rw [show (m==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
      rfl,
    isPrincipalP_T m hm]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (T m) 0==0 && Trans.Recal.gp1 (T m) 0==0)=false from by
    rw [show Trans.Recal.gp0 (T m) 0=1 from by
        simpa only [p_phase0 0] using gp0_T m 0 (by omega),
      show Trans.Recal.gp1 (T m) 0=0 from by
        simpa only [q_phase0 0] using gp1_T m 0 (by omega)]
    rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (T m) 0==0)=true from by
    rw [show Trans.Recal.gp1 (T m) 0=0 from by
      simpa only [q_phase0 0] using gp1_T m 0 (by omega)]
    rfl]
  simp only [if_true]
  rw [show Trans.Recal.incrFirst (T m) (-Trans.Recal.gp0 (T m) 0)=S m from by
    rw [show Trans.Recal.gp0 (T m) 0=1 from by
      simpa only [p_phase0 0] using gp0_T m 0 (by omega)]
    rfl]
  exact hred

theorem red_L_succ_from_tail (m f : Nat)
    (htail : Trans.Recal.red (f+3) (T (m+1))=S (m+1)) :
    Trans.Recal.red (f+4) (L (m+1))=L (m+1) := by
  rw [show f+4=(f+3)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L (m+1))=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp,
    isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L (m+1)) 0==0 &&
      Trans.Recal.gp1 (L (m+1)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L]
  rw [show Trans.Recal.lenI (L (m+1))-1=((m+5:Nat):Int) from by
    rw [lenI_L]; omega]
  rw [show ((1:Int)==((m+5:Nat):Int))=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L_succ,firstNodes_L_succ,joints_L_succ]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 4=[0,1,2,3] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 0 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 1 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 2 []=[(2,0)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 3 []=T (m+1) from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 1 0=3 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 2 0=4 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 3 0=5 from rfl,
    show ([1,1,1,0]:List Int).getD 0 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 1 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 2 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 3 0=0 from rfl]
  rw [show Trans.Recal.gp1 [(2,1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_L_two]
  rw [show Trans.Recal.gp1 [(2,0)] 0=0 from rfl,
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [fpar1_L_three]
  rw [show Trans.Recal.gp1 (T (m+1)) 0=0 from by
      simpa only [q_phase0 0] using gp1_T (m+1) 0 (by omega),
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  change (((Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,0)]) 2)++
    Trans.Recal.incrFirst
      (Trans.Recal.red (f+3) ((1,0)::Trans.Recal.derp (T (m+1)))) 1=L (m+1)
  rw [cons_derp_T,htail,incrFirst_S]
  have hx : Trans.Recal.red (f+3) [(2,1)]=[(1,1)] := by
    change Trans.Recal.red (f+3) G1.X1=[(1,1)]
    simpa only [show f+3=(f+1)+2 by omega] using G1.red_X1 (f+1)
  have hz : Trans.Recal.red (f+3) [(2,0)]=[(0,0)] := by
    simpa only [show f+3=(f+2)+1 by omega] using red_single_zero (f+2)
  rw [hx,hz]
  rfl

theorem red_L_bound : ∀ m f : Nat, 4*m+8≤f →
    Trans.Recal.red f (L m)=L m := by
  intro m
  refine Nat.strongRecOn (motive:=fun m=>∀ f:Nat,4*m+8≤f→
    Trans.Recal.red f (L m)=L m) m ?_
  intro m ih f hf
  cases m with
  | zero =>
    obtain ⟨g,rfl⟩ : ∃ g,f=g+4 := ⟨f-4,by omega⟩
    exact red_L_zero g
  | succ m =>
    obtain ⟨g,rfl⟩ : ∃ g,f=g+4 := ⟨f-4,by omega⟩
    apply red_L_succ_from_tail m g
    by_cases h1:m+1=1
    · have hm:m=0:=by omega
      subst m
      simpa only [show g+3=(g+2)+1 by omega] using red_T_one (g+2)
    · have hm2:2≤m+1:=by omega
      apply red_T_step (m+1) (g+2) hm2
      by_cases h5:m+1<5
      · have hc:m+1=2∨m+1=3∨m+1=4:=by omega
        rcases hc with hc|hc|hc
        · rw [hc,S_two]
          obtain ⟨u,hu⟩ : ∃ u,g+2=u+3 := ⟨g-1,by omega⟩
          rw [hu]
          exact red_LG 0 u
        · rw [hc,S_three]
          obtain ⟨u,hu⟩ : ∃ u,g+2=u+3 := ⟨g-1,by omega⟩
          rw [hu]
          exact red_LG 1 u
        · rw [hc,S_four]
          obtain ⟨u,hu⟩ : ∃ u,g+2=u+3 := ⟨g-1,by omega⟩
          rw [hu]
          exact red_LG 2 u
      · obtain ⟨k,hk⟩ : ∃ k,m+1=k+5 := ⟨m+1-5,by omega⟩
        rw [hk,S_add_five]
        exact ih k (by omega) (g+2) (by omega)

theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  unfold Trans.Recal.redP
  apply red_L_bound
  unfold Trans.Recal.redFuel
  rw [length_L]
  omega

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  exact G1.beq_PS_self _

-/

/-! ### Six-phase reader data. -/

theorem gp1_L_tail (m k : Nat) (hk : 6≤k) (hkm : k<m+6) :
    Trans.Recal.gp1 (L m) (k:Int)=q (k-6) := by
  rw [gp1_L m k hkm,if_neg (by omega)]

theorem gp0_L_tail_phase0 (a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp0 (L m) ((6*a+6:Nat):Int)=((2*a+2:Nat):Int) := by
  rw [gp0_L m (6*a+6) (by omega),if_neg (by omega)]
  simpa only [show 6*a+6-6=6*a by omega] using p_phase0 a

theorem gp1_L_phase0_tail (a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp1 (L m) ((6*a+6:Nat):Int)=0 := by
  rw [gp1_L_tail m (6*a+6) (by omega) (by omega)]
  simpa only [show 6*a+6-6=6*a by omega] using q_phase0 a

theorem gp1_L_phase1_tail (a m : Nat) (h : 6*a+1<m) :
    Trans.Recal.gp1 (L m) ((6*a+7:Nat):Int)=1 := by
  rw [gp1_L_tail m (6*a+7) (by omega) (by omega)]
  simpa only [show 6*a+7-6=6*a+1 by omega] using q_phase1 a

theorem gp1_L_phase2_tail (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.gp1 (L m) ((6*a+8:Nat):Int)=1 := by
  rw [gp1_L_tail m (6*a+8) (by omega) (by omega)]
  simpa only [show 6*a+8-6=6*a+2 by omega] using q_phase2 a

theorem gp1_L_phase3_tail (a m : Nat) (h : 6*a+3<m) :
    Trans.Recal.gp1 (L m) ((6*a+9:Nat):Int)=1 := by
  rw [gp1_L_tail m (6*a+9) (by omega) (by omega)]
  simpa only [show 6*a+9-6=6*a+3 by omega] using q_phase3 a

theorem gp1_L_phase4_tail (a m : Nat) (h : 6*a+4<m) :
    Trans.Recal.gp1 (L m) ((6*a+10:Nat):Int)=0 := by
  rw [gp1_L_tail m (6*a+10) (by omega) (by omega)]
  simpa only [show 6*a+10-6=6*a+4 by omega] using q_phase4 a

theorem gp1_L_phase5_tail (a m : Nat) (h : 6*a+5<m) :
    Trans.Recal.gp1 (L m) ((6*a+11:Nat):Int)=1 := by
  rw [gp1_L_tail m (6*a+11) (by omega) (by omega)]
  simpa only [show 6*a+11-6=6*a+5 by omega] using q_phase5 a

theorem gp1_L_before_phase0 (a m : Nat) (h : 6*a<m) :
    Trans.Recal.gp1 (L m) ((6*a+5:Nat):Int)=1 := by
  cases a with
  | zero => rfl
  | succ a =>
    simpa only [show 6*(a+1)+5=6*a+11 by omega] using
      gp1_L_phase5_tail a m (by omega)

theorem fpar1_L_phase0_lb (a m : Nat) (h : 6*a<m) :
    Trans.Recal.fpar (L m) 1 ((6*a+6:Nat):Int) ((6*a+5:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L,gp1_L_phase0_tail a m h]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) ((6*a+6:Nat):Int) ((6*a+5:Nat):Int)=
      ((6*a+5:Nat):Int) from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L_tail_phase0 a m h]
    change Trans.Recal.fpar0Aux (m+7) (L m) ((2*a+2:Nat):Int)
      (((6*a+6:Nat):Int)-1) ((6*a+5:Nat):Int)=((6*a+5:Nat):Int)
    rw [show m+7=(m+6)+1 by omega,Trans.Recal.fpar0Aux,
      show ((6*a+6:Nat):Int)-1=((6*a+5:Nat):Int) by omega,
      if_neg (by omega),gp0_L_before_phase0 a m h,if_pos (by omega)],
    if_neg (by omega),gp1_L_before_phase0 a m h,if_neg (by omega)]
  rw [show Trans.Recal.fpar0 (L m) ((6*a+5:Nat):Int) ((6*a+5:Nat):Int)=-1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rw [if_pos (by omega)],if_pos (by omega)]

theorem fpar1_L_phase2_lb (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.fpar (L m) 1 ((6*a+8:Nat):Int) ((6*a+7:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L,gp1_L_phase2_tail a m h]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) ((6*a+8:Nat):Int) ((6*a+7:Nat):Int)=
      ((6*a+7:Nat):Int) from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    rw [show Trans.Recal.gp0 (L m) ((6*a+8:Nat):Int)=((2*a+4:Nat):Int) from
      gp0_L_phase2 a m h]
    simp only [Trans.Recal.fpar0Aux]
    rw [show ((6*a+8:Nat):Int)-1=((6*a+7:Nat):Int) by omega,
      if_neg (by omega)]
    rw [show Trans.Recal.gp0 (L m) ((6*a+7:Nat):Int)=((2*a+3:Nat):Int) from
      gp0_L_phase1 a m (by omega),
      if_pos (by omega)],
    if_neg (by omega),gp1_L_phase1_tail a m (by omega),if_neg (by omega)]
  rw [show Trans.Recal.fpar0 (L m) ((6*a+7:Nat):Int) ((6*a+7:Nat):Int)=-1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rw [if_pos (by omega)],if_pos (by omega)]

theorem isAdm_L_before_phase0 (a m : Nat) (h : 6*a<m) :
    Trans.Recal.isAdm (L m) ((6*a+5:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((6*a+5:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  rw [show ((6*a+5:Nat):Int)+1=((6*a+6:Nat):Int) by omega]
  have hp : Trans.Recal.isParentP (L m) 1 ((6*a+6:Nat):Int)
      ((6*a+5:Nat):Int)=false := by
    unfold Trans.Recal.isParentP
    rw [fpar1_L_phase0_lb a m h,lenI_L]
    rw [show decide (0≤((6*a+5:Nat):Int))=true from decide_eq_true (by omega),
      show decide (((6*a+5:Nat):Int)<(m:Int)+6)=true from decide_eq_true (by omega),
      show (((6*a+5:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
    rfl
  rw [hp,Bool.and_false]
  rfl

theorem isAdm_L_phase0_at (a m : Nat) (h : 6*a<m) :
    Trans.Recal.isAdm (L m) ((6*a+6:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((6*a+6:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  rw [show ((6*a+6:Nat):Int)-1=((6*a+5:Nat):Int) by omega]
  have hp : Trans.Recal.isParentP (L m) 1 ((6*a+6:Nat):Int)
      ((6*a+5:Nat):Int)=false := by
    unfold Trans.Recal.isParentP
    rw [fpar1_L_phase0_lb a m h,lenI_L]
    rw [show decide (0≤((6*a+5:Nat):Int))=true from decide_eq_true (by omega),
      show decide (((6*a+5:Nat):Int)<(m:Int)+6)=true from decide_eq_true (by omega),
      show (((6*a+5:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
    rfl
  rw [hp,Bool.false_and]
  rfl

theorem isAdm_L_phase1_at (a m : Nat) (h : 6*a+2<m) :
    Trans.Recal.isAdm (L m) ((6*a+7:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((6*a+7:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  rw [show ((6*a+7:Nat):Int)+1=((6*a+8:Nat):Int) by omega]
  have hp : Trans.Recal.isParentP (L m) 1 ((6*a+8:Nat):Int)
      ((6*a+7:Nat):Int)=false := by
    unfold Trans.Recal.isParentP
    rw [fpar1_L_phase2_lb a m h,lenI_L]
    rw [show decide (0≤((6*a+7:Nat):Int))=true from decide_eq_true (by omega),
      show decide (((6*a+7:Nat):Int)<(m:Int)+6)=true from decide_eq_true (by omega),
      show (((6*a+7:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
    rfl
  rw [hp,Bool.and_false]
  rfl

theorem adm_L_new1 (a : Nat) :
    Trans.Recal.adm (L (6*a+1)) ((6*a+5:Nat):Int)=((6*a+5:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_before_phase0 a (6*a+1) (by omega),if_pos rfl]

theorem adm_L_new2 (a : Nat) :
    Trans.Recal.adm (L (6*a+2)) ((6*a+6:Nat):Int)=((6*a+6:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase0_at a (6*a+2) (by omega),if_pos rfl]

theorem adm_L_new3 (a : Nat) :
    Trans.Recal.adm (L (6*a+3)) ((6*a+7:Nat):Int)=((6*a+7:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a (6*a+3) (by omega),if_pos rfl]

theorem adm_L_new4 (a : Nat) :
    Trans.Recal.adm (L (6*a+4)) ((6*a+7:Nat):Int)=((6*a+7:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a (6*a+4) (by omega),if_pos rfl]

theorem adm_L_new5 (a : Nat) :
    Trans.Recal.adm (L (6*a+5)) ((6*a+7:Nat):Int)=((6*a+7:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a (6*a+5) (by omega),if_pos rfl]

theorem adm_L_new6 (a : Nat) :
    Trans.Recal.adm (L (6*a+6)) ((6*a+6:Nat):Int)=((6*a+6:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase0_at a (6*a+6) (by omega),if_pos rfl]

theorem j0_L_new1 (a : Nat) :
    Trans.Recal.fpar (L (6*a+1)) 0 ((6*a+6:Nat):Int) 0=((6*a+5:Nat):Int) :=
  fpar_L_phase0 a (6*a+1) (by omega)

theorem j0_L_new2 (a : Nat) :
    Trans.Recal.fpar (L (6*a+2)) 0 ((6*a+7:Nat):Int) 0=((6*a+6:Nat):Int) :=
  fpar_L_phase1 a (6*a+2) (by omega)

theorem j0_L_new3 (a : Nat) :
    Trans.Recal.fpar (L (6*a+3)) 0 ((6*a+8:Nat):Int) 0=((6*a+7:Nat):Int) :=
  fpar_L_phase2 a (6*a+3) (by omega)

theorem j0_L_new4 (a : Nat) :
    Trans.Recal.fpar (L (6*a+4)) 0 ((6*a+9:Nat):Int) 0=((6*a+7:Nat):Int) :=
  fpar_L_phase3 a (6*a+4) (by omega)

theorem j0_L_new5 (a : Nat) :
    Trans.Recal.fpar (L (6*a+5)) 0 ((6*a+10:Nat):Int) 0=((6*a+7:Nat):Int) :=
  fpar_L_phase4 a (6*a+5) (by omega)

theorem j0_L_new6 (a : Nat) :
    Trans.Recal.fpar (L (6*a+6)) 0 ((6*a+11:Nat):Int) 0=((6*a+6:Nat):Int) :=
  fpar_L_phase5 a (6*a+6) (by omega)

theorem transType_L_new1 (a : Nat) :
    Trans.Recal.transTypeMain (L (6*a+1)) ((6*a+5:Nat):Int)
      ((6*a+6:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase0_tail a (6*a+1) (by omega)]
  simp only [show ((0:Int)==0)=true from rfl,if_true]
  rw [isAdm_L_before_phase0 a (6*a+1) (by omega),if_pos rfl]

theorem transType_L_new2 (a : Nat) :
    Trans.Recal.transTypeMain (L (6*a+2)) ((6*a+6:Nat):Int)
      ((6*a+7:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase1_tail a (6*a+2) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase0_tail a (6*a+2) (by omega),if_neg (by omega),if_neg (by omega)]

theorem transType_L_new3 (a : Nat) :
    Trans.Recal.transTypeMain (L (6*a+3)) ((6*a+7:Nat):Int)
      ((6*a+8:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase2_tail a (6*a+3) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase1_tail a (6*a+3) (by omega),if_pos (by omega),
    isAdm_L_phase1_at a (6*a+3) (by omega),if_pos rfl]

theorem transType_L_new4 (a : Nat) :
    Trans.Recal.transTypeMain (L (6*a+4)) ((6*a+7:Nat):Int)
      ((6*a+9:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase3_tail a (6*a+4) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase1_tail a (6*a+4) (by omega),if_pos (by omega),
    isAdm_L_phase1_at a (6*a+4) (by omega),if_pos rfl]

theorem transType_L_new5 (a : Nat) :
    Trans.Recal.transTypeMain (L (6*a+5)) ((6*a+7:Nat):Int)
      ((6*a+10:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase4_tail a (6*a+5) (by omega)]
  simp only [show ((0:Int)==0)=true from rfl,if_true]
  rw [isAdm_L_phase1_at a (6*a+5) (by omega),if_pos rfl]

theorem transType_L_new6 (a : Nat) :
    Trans.Recal.transTypeMain (L (6*a+6)) ((6*a+6:Nat):Int)
      ((6*a+11:Nat):Int)=5 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase5_tail a (6*a+6) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase0_tail a (6*a+6) (by omega),if_neg (by omega),if_pos (by omega)]

theorem mkC2_L_new1 (a : Nat) :
    Trans.Recal.mkC2 (L (6*a+1)) ((6*a+5:Nat):Int) ((6*a+6:Nat):Int)
      1 D1z=.D 1 D0z := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase0_tail a (6*a+1) (by omega)]
  rfl

theorem mkC2_L_new2 (a : Nat) :
    Trans.Recal.mkC2 (L (6*a+2)) ((6*a+6:Nat):Int) ((6*a+7:Nat):Int)
      6 D0z=.D 0 D1z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L_phase1_tail a (6*a+2) (by omega)]
  rfl

theorem mkC2_L_new3 (a : Nat) :
    Trans.Recal.mkC2 (L (6*a+3)) ((6*a+7:Nat):Int) ((6*a+8:Nat):Int)
      3 D1z=D11z := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase2_tail a (6*a+3) (by omega)]
  rfl

theorem mkC2_L_new4 (a : Nat) :
    Trans.Recal.mkC2 (L (6*a+4)) ((6*a+7:Nat):Int) ((6*a+9:Nat):Int)
      3 D11z=D1ss := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase3_tail a (6*a+4) (by omega)]
  rfl

theorem mkC2_L_new5 (a : Nat) :
    Trans.Recal.mkC2 (L (6*a+5)) ((6*a+7:Nat):Int) ((6*a+10:Nat):Int)
      1 D1ss=A0 := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase4_tail a (6*a+5) (by omega)]
  rfl

theorem mkC2_L_new6 (a : Nat) :
    Trans.Recal.mkC2 (L (6*a+6)) ((6*a+6:Nat):Int) ((6*a+11:Nat):Int)
      5 Anchor=.D 0 (Part 0) := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus Part
  rw [gp1_L_phase5_tail a (6*a+6) (by omega)]
  rfl

theorem LBT_phase0 (a : Nat) : LBT (6*a)=.D 0 (W a (Part 0)) := by
  unfold LBT
  rw [show 6*a/6=a by omega,show 6*a%6=0 by omega]

theorem LBT_phase1 (a : Nat) : LBT (6*a+1)=.D 0 (W a (Part 1)) := by
  unfold LBT
  rw [show (6*a+1)/6=a by omega,show (6*a+1)%6=1 by omega]

theorem LBT_phase2 (a : Nat) : LBT (6*a+2)=.D 0 (W a (Part 2)) := by
  unfold LBT
  rw [show (6*a+2)/6=a by omega,show (6*a+2)%6=2 by omega]

theorem LBT_phase3 (a : Nat) : LBT (6*a+3)=.D 0 (W a (Part 3)) := by
  unfold LBT
  rw [show (6*a+3)/6=a by omega,show (6*a+3)%6=3 by omega]

theorem LBT_phase4 (a : Nat) : LBT (6*a+4)=.D 0 (W a (Part 4)) := by
  unfold LBT
  rw [show (6*a+4)/6=a by omega,show (6*a+4)%6=4 by omega]

theorem LBT_phase5 (a : Nat) : LBT (6*a+5)=.D 0 (W a (Part 5)) := by
  unfold LBT
  rw [show (6*a+5)/6=a by omega,show (6*a+5)%6=5 by omega]

theorem LBT_phase6 (a : Nat) : LBT (6*a+6)=.D 0 (W (a+1) (Part 0)) := by
  simpa only [show 6*a+6=6*(a+1) by omega] using LBT_phase0 (a+1)

theorem repl_D0W : ∀ (a f r : Nat) (b bb c cc : Trans.Dict.BT),
    (∀ g : Nat, r≤g → Trans.Recal.replMark g (.D 0 b) c cc=some (.D 0 bb)) →
    (∀ n : Nat, ((Trans.Dict.BT.D 0 (W (n+1) b))==c)=false ∧
      ((Trans.Dict.BT.D 1 (.D 0 (W n b)))==c)=false) →
    4*a+r≤f →
    Trans.Recal.replMark f (.D 0 (W a b)) c cc=some (.D 0 (W a bb))
  | 0,f,r,b,bb,c,cc,hbase,_,hf => hbase f (by simpa using hf)
  | a+1,f,r,b,bb,c,cc,hbase,hne,hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+4 := ⟨f-4,by omega⟩
    change Trans.Recal.replMark (g+4) (.D 0 (.sum A0 (.D 1 (.D 0 (W a b))))) c cc=
      some (.D 0 (.sum A0 (.D 1 (.D 0 (W a bb)))))
    rw [show g+4=(g+3)+1 by omega,Trans.Recal.replMark]
    have hn:=(hne a).1
    change ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.D 0 (W a b)))))==c)=false at hn
    rw [hn]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum A0 (.D 1 (.D 0 (W a b))))=
      [A0,.D 1 (.D 0 (W a b))] from rfl]
    change ((Trans.Recal.replMark (g+2) (.D 1 (.D 0 (W a b))) c cc).map
      (fun x=>Trans.Dict.BT.sum A0 x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
    rw [(hne a).2]
    simp only [Bool.false_eq_true,if_false]
    change (((Trans.Recal.replMark (g+1) (.D 0 (W a b)) c cc).map
      (fun x=>Trans.Dict.BT.D 1 x)).map
      (fun x=>Trans.Dict.BT.sum A0 x)).map (fun x=>Trans.Dict.BT.D 0 x)=
        some (Trans.Dict.BT.D 0
          (Trans.Dict.BT.sum A0 (.D 1 (.D 0 (W a bb)))))
    rw [repl_D0W a (g+1) r b bb c cc hbase hne (by omega)]
    rfl

theorem W_add (a b : Nat) (c : Trans.Dict.BT) : W a (W b c)=W (a+b) c := by
  induction a with
  | zero => simp [W]
  | succ a ih =>
    simp only [W,ih]
    rw [show a+1+b=(a+b)+1 by omega,W]

theorem repl_LBT_phase0 (a f : Nat) (hf : 4*a+3≤f) :
    Trans.Recal.replMark f (LBT (6*a)) D1z (.D 1 D0z)=
      some (LBT (6*a+1)) := by
  rw [LBT_phase0,LBT_phase1]
  exact repl_D0W a f 3 (Part 0) (Part 1) D1z (.D 1 D0z)
    (fun g hg => by
      obtain ⟨h,rfl⟩ : ∃ h,g=h+3 := ⟨g-3,by omega⟩
      change Trans.Recal.replMark (h+3) (.D 0 (.sum A0 D1z)) D1z (.D 1 D0z)=
        some (.D 0 (.sum A0 (.D 1 D0z)))
      rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark]
      rw [show ((Trans.Dict.BT.D 0 (.sum A0 D1z))==D1z)=false from rfl]
      simp only [Bool.false_eq_true,if_false]
      rw [Trans.Recal.replMark]
      change ((Trans.Recal.replMark (h+1) D1z D1z (.D 1 D0z)).map
        (fun x=>Trans.Dict.BT.sum A0 x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
      rw [G1.replMark_self (h+1) 1 .zero (.D 1 D0z) (by omega)]
      rfl)
    (fun n => by constructor <;> cases n <;> rfl) hf

theorem repl_LBT_phase1 (a f : Nat) (hf : 4*a+4≤f) :
    Trans.Recal.replMark f (LBT (6*a+1)) D0z (.D 0 D1z)=
      some (LBT (6*a+2)) := by
  rw [LBT_phase1,LBT_phase2]
  apply repl_D0W a f 4 (Part 1) (Part 2) D0z (.D 0 D1z) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+4 := ⟨g-4,by omega⟩
    simp only [Part]
    change Trans.Recal.replMark (h+4) (.D 0 (.sum A0 (.D 1 D0z))) D0z (.D 0 D1z)=
      some (.D 0 (.sum A0 (.D 1 (.D 0 D1z))))
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 D0z)))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum A0 (.D 1 D0z))=[A0,.D 1 D0z] from rfl]
    change ((Trans.Recal.replMark (h+2) (.D 1 D0z) D0z (.D 0 D1z)).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 1 D0z)==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change (((Trans.Recal.replMark (h+1) D0z D0z (.D 0 D1z)).map
      (fun q=>Trans.Dict.BT.D 1 q)).map (fun q=>Trans.Dict.BT.sum A0 q)).map
        (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [G1.replMark_self (h+1) 0 .zero (.D 0 D1z) (by omega)]
    rfl
  · intro n
    constructor <;> cases n <;> rfl

theorem repl_LBT_phase2 (a f : Nat) (hf : 4*a+5≤f) :
    Trans.Recal.replMark f (LBT (6*a+2)) D1z D11z=
      some (LBT (6*a+3)) := by
  rw [LBT_phase2,LBT_phase3]
  apply repl_D0W a f 5 (Part 2) (Part 3) D1z D11z ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
    simp only [Part]
    change Trans.Recal.replMark (h+5) (.D 0 (.sum A0 (.D 1 (.D 0 D1z)))) D1z D11z=
      some (.D 0 (.sum A0 (.D 1 (.D 0 D11z))))
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.D 0 D1z))))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum A0 (.D 1 (.D 0 D1z)))=
      [A0,.D 1 (.D 0 D1z)] from rfl]
    change ((Trans.Recal.replMark (h+3) (.D 1 (.D 0 D1z)) D1z D11z).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 1 (.D 0 D1z))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 D1z)==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change ((((Trans.Recal.replMark (h+1) D1z D1z D11z).map
      (fun q=>Trans.Dict.BT.D 0 q)).map (fun q=>Trans.Dict.BT.D 1 q)).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map
        (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [G1.replMark_self (h+1) 1 .zero D11z (by omega)]
    rfl
  · intro n
    constructor <;> cases n <;> rfl

theorem repl_LBT_phase3 (a f : Nat) (hf : 4*a+5≤f) :
    Trans.Recal.replMark f (LBT (6*a+3)) D11z D1ss=
      some (LBT (6*a+4)) := by
  rw [LBT_phase3,LBT_phase4]
  apply repl_D0W a f 5 (Part 3) (Part 4) D11z D1ss ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
    simp only [Part]
    change Trans.Recal.replMark (h+5) (.D 0 (.sum A0 (.D 1 (.D 0 D11z)))) D11z D1ss=
      some (.D 0 (.sum A0 (.D 1 (.D 0 D1ss))))
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.D 0 D11z))))==D11z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum A0 (.D 1 (.D 0 D11z)))=
      [A0,.D 1 (.D 0 D11z)] from rfl]
    change ((Trans.Recal.replMark (h+3) (.D 1 (.D 0 D11z)) D11z D1ss).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 1 (.D 0 D11z))==D11z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 D11z)==D11z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change ((((Trans.Recal.replMark (h+1) D11z D11z D1ss).map
      (fun q=>Trans.Dict.BT.D 0 q)).map (fun q=>Trans.Dict.BT.D 1 q)).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map
        (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [G1.replMark_self (h+1) 1 D1z D1ss (by omega)]
    rfl
  · intro n
    constructor <;> cases n <;> rfl

theorem repl_LBT_phase4 (a f : Nat) (hf : 4*a+5≤f) :
    Trans.Recal.replMark f (LBT (6*a+4)) D1ss A0=
      some (LBT (6*a+5)) := by
  rw [LBT_phase4,LBT_phase5]
  apply repl_D0W a f 5 (Part 4) (Part 5) D1ss A0 ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
    simp only [Part]
    change Trans.Recal.replMark (h+5) (.D 0 (.sum A0 (.D 1 (.D 0 D1ss)))) D1ss A0=
      some (.D 0 (.sum A0 (.D 1 (.D 0 A0))))
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.D 0 D1ss))))==D1ss)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum A0 (.D 1 (.D 0 D1ss)))=
      [A0,.D 1 (.D 0 D1ss)] from rfl]
    change ((Trans.Recal.replMark (h+3) (.D 1 (.D 0 D1ss)) D1ss A0).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 1 (.D 0 D1ss))==D1ss)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 D1ss)==D1ss)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change ((((Trans.Recal.replMark (h+1) D1ss D1ss A0).map
      (fun q=>Trans.Dict.BT.D 0 q)).map (fun q=>Trans.Dict.BT.D 1 q)).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map
        (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [G1.replMark_self (h+1) 1 (.sum D1z D1z) A0 (by omega)]
    rfl
  · intro n
    constructor <;> cases n <;> rfl

theorem repl_LBT_phase5 (a f : Nat) (hf : 4*a+4≤f) :
    Trans.Recal.replMark f (LBT (6*a+5)) Anchor (.D 0 (Part 0))=
      some (LBT (6*a+6)) := by
  rw [LBT_phase5,LBT_phase6]
  have h := repl_D0W a f 4 (Part 5) (W 1 (Part 0)) Anchor (.D 0 (Part 0))
    (fun g hg => by
      obtain ⟨h,rfl⟩ : ∃ h,g=h+4 := ⟨g-4,by omega⟩
      simp only [Part]
      change Trans.Recal.replMark (h+4) (.D 0 (.sum A0 (.D 1 (.D 0 A0))) )
        Anchor (.D 0 (Part 0))=
          some (.D 0 (.sum A0 (.D 1 (.D 0 (Part 0)))))
      rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
      rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.D 0 A0))))==Anchor)=false from rfl]
      simp only [Bool.false_eq_true,if_false]
      rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark]
      rw [show Trans.Dict.BT.toL (.sum A0 (.D 1 (.D 0 A0)))=
        [A0,.D 1 (.D 0 A0)] from rfl]
      change ((Trans.Recal.replMark (h+2) (.D 1 (.D 0 A0)) Anchor
        (.D 0 (Part 0))).map (fun x=>Trans.Dict.BT.sum A0 x)).map
          (fun x=>Trans.Dict.BT.D 0 x)=_
      rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark]
      rw [show ((Trans.Dict.BT.D 1 (.D 0 A0))==Anchor)=false from rfl]
      simp only [Bool.false_eq_true,if_false]
      change (((Trans.Recal.replMark (h+1) Anchor Anchor (.D 0 (Part 0))).map
        (fun x=>Trans.Dict.BT.D 1 x)).map
        (fun x=>Trans.Dict.BT.sum A0 x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
      rw [G1.replMark_self (h+1) 0 A0 (.D 0 (Part 0)) (by omega)]
      rfl)
    (fun n => by constructor <;> cases n <;> rfl) hf
  rw [W_add] at h
  simpa only [show a+1=a+1 by rfl] using h

/-! ### Memo invariant. -/

def Allowed (k : Nat) (req : Option Int) : Prop :=
  if k%6=0 then req=none ∨ req=some ((k+5:Nat):Int)
  else if k%6=1 then req=none ∨ req=some ((k+5:Nat):Int)
  else if k%6=2 then
    req=none ∨ req=some ((k+4:Nat):Int) ∨ req=some ((k+5:Nat):Int)
  else if k%6=3 then
    req=none ∨ req=some ((k+3:Nat):Int) ∨ req=some ((k+4:Nat):Int)
  else if k%6=4 then
    req=none ∨ req=some ((k+2:Nat):Int) ∨ req=some ((k+3:Nat):Int)
  else req=none ∨ req=some ((k+1:Nat):Int)

def Val (k : Nat) (req : Option Int) : Trans.Dict.BT :=
  if req=none then LBT k
  else if k%6=0 then D1z
  else if k%6=1 then D0z
  else if k%6=2 then
    if req=some ((k+4:Nat):Int) then .D 0 D1z else D1z
  else if k%6=3 then
    if req=some ((k+3:Nat):Int) then .D 0 D11z else D11z
  else if k%6=4 then
    if req=some ((k+2:Nat):Int) then .D 0 D1ss else D1ss
  else Anchor

theorem Allowed_none (k : Nat) : Allowed k none := by
  simp [Allowed]

theorem Val_none (k : Nat) : Val k none=LBT k := by simp [Val]

theorem Allowed_phase0 (a : Nat) :
    Allowed (6*a) (some ((6*a+5:Nat):Int)) := by
  rw [Allowed,if_pos (by omega)]
  exact Or.inr rfl

theorem Allowed_phase1 (a : Nat) :
    Allowed (6*a+1) (some ((6*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_pos (by omega)]
  exact Or.inr (by congr 2 <;> omega)

theorem Allowed_phase2 (a : Nat) :
    Allowed (6*a+2) (some ((6*a+7:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Allowed_phase2carry (a : Nat) :
    Allowed (6*a+2) (some ((6*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inl (by congr 2 <;> omega))

theorem Allowed_phase3 (a : Nat) :
    Allowed (6*a+3) (some ((6*a+7:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Allowed_phase3carry (a : Nat) :
    Allowed (6*a+3) (some ((6*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inl (by congr 2 <;> omega))

theorem Allowed_phase4 (a : Nat) :
    Allowed (6*a+4) (some ((6*a+7:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
    if_pos (by omega)]
  exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Allowed_phase4carry (a : Nat) :
    Allowed (6*a+4) (some ((6*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
    if_pos (by omega)]
  exact Or.inr (Or.inl (by congr 2 <;> omega))

theorem Allowed_phase5 (a : Nat) :
    Allowed (6*a+5) (some ((6*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
    if_neg (by omega)]
  exact Or.inr (by congr 2 <;> omega)

theorem Val_phase0 (a : Nat) :
    Val (6*a) (some ((6*a+5:Nat):Int))=D1z := by
  rw [Val,if_neg (by intro h; cases h),if_pos (by omega)]

theorem Val_phase1 (a : Nat) :
    Val (6*a+1) (some ((6*a+6:Nat):Int))=D0z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_pos (by omega)]

theorem Val_phase2 (a : Nat) :
    Val (6*a+2) (some ((6*a+7:Nat):Int))=D1z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_pos (by omega),if_neg (by intro h; injection h with h; omega)]

theorem Val_phase2carry (a : Nat) :
    Val (6*a+2) (some ((6*a+6:Nat):Int))=.D 0 D1z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_pos (by omega),if_pos (by congr 2 <;> omega)]

theorem Val_phase3 (a : Nat) :
    Val (6*a+3) (some ((6*a+7:Nat):Int))=D11z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_pos (by omega),if_neg (by intro h; injection h with h; omega)]

theorem Val_phase3carry (a : Nat) :
    Val (6*a+3) (some ((6*a+6:Nat):Int))=.D 0 D11z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_pos (by omega),if_pos (by congr 2 <;> omega)]

theorem Val_phase4 (a : Nat) :
    Val (6*a+4) (some ((6*a+7:Nat):Int))=D1ss := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_neg (by omega),if_pos (by omega),
    if_neg (by intro h; injection h with h; omega)]

theorem Val_phase4carry (a : Nat) :
    Val (6*a+4) (some ((6*a+6:Nat):Int))=.D 0 D1ss := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_neg (by omega),if_pos (by omega),
    if_pos (by congr 2 <;> omega)]

theorem Val_phase5 (a : Nat) :
    Val (6*a+5) (some ((6*a+6:Nat):Int))=Anchor := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_neg (by omega),if_neg (by omega)]

theorem L_inj (a b : Nat) (h : L a=L b) : a=b := by
  have hl:=congrArg List.length h
  rw [length_L,length_L] at hl
  omega

theorem L_ne_LG (k j : Nat) : L k≠G1.LG j := by
  intro h
  have hd:=congrArg (fun z=>z.getD 4 ((9:Int),(9:Int))) h
  rcases j with _|j
  · simp [L,G1.LG] at hd
  · rcases j with _|j
    · simp [L,G1.LG] at hd
    · rcases j with _|j
      · simp [L,G1.LG] at hd
      · simp [L,G1.LG,List.replicate_succ] at hd

theorem L_ne_base (k : Nat) : L k≠G1.Base := by
  intro h
  have hl:=congrArg List.length h
  rw [length_L] at hl
  simp [G1.Base] at hl

theorem L_ne_G9L (k j : Nat) : L k≠G9.L j := by
  intro h
  have hd:=congrArg (fun z=>z.getD 5 ((9:Int),(9:Int))) h
  cases j with
  | zero => simp [L,G9.L,G9.T] at hd
  | succ j =>
    simp [L,G9.L,G9.T,G9.p,G9.q,List.range_succ_eq_map] at hd

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  G1.Good p ∧
    (∀ j, p.1=(G1.LG j,some 0) → p.2=G1.LBT j) ∧
    (∀ j req, p.1=(G9.L j,req) → G9.Allowed j req → p.2=G9.Val j req) ∧
    ∀ k req, p.1=(L k,req) → Allowed k req → p.2=Val k req

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p∈tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem good_L_entry (k : Nat) (req : Option Int) (hr : Allowed k req) :
    Good ((L k,req),Val k req) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      exact absurd (congrArg Prod.fst h) (L_ne_LG k j)
    · intro j h
      exact absurd (congrArg Prod.fst h) (L_ne_LG k j)
    · intro h
      exact absurd (congrArg Prod.fst h) (L_ne_base k)
  · constructor
    · intro j h
      exact absurd (congrArg Prod.fst h) (L_ne_LG k j)
    · constructor
      · intro j r h _
        exact absurd (congrArg Prod.fst h) (L_ne_G9L k j)
      · intro j r h _
        have hL:L k=L j:=congrArg Prod.fst h
        have hkj:=L_inj k j hL
        subst hkj
        have hreq:req=r:=by simpa using congrArg Prod.snd h
        subst hreq
        rfl

theorem good_LG_entry (k : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 1) : Good ((G1.LG k,req),G1.Val k req) := by
  constructor
  · have hs:=G1.Sound_cons [] G1.Sound_nil k req
    exact hs _ (by simp)
  · constructor
    · intro j h
      have hk:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hk
      have hreq:req=some 0:=by simpa using congrArg Prod.snd h
      rcases hr with hr|hr <;> subst hr <;> cases hreq
    · constructor
      · intro j r h ha
        have hg9:=G9.good_LG_entry k req hr
        exact hg9.2.2 j r h ha
      · intro j r h _
        exact absurd (congrArg Prod.fst h).symm (L_ne_LG j k)

theorem good_base_entry :
    Good ((G1.Base,(none:Option Int)),Trans.Dict.BT.zero) := by
  constructor
  · have hs:=G1.Sound_cons_base [] G1.Sound_nil
    exact hs _ (by simp)
  · constructor
    · intro j h
      exact absurd (congrArg Prod.fst h).symm (G1.LG_ne_base j)
    · constructor
      · intro j r h ha
        exact (G9.good_base_entry).2.2 j r h ha
      · intro j r h _
        exact absurd (congrArg Prod.fst h).symm (L_ne_base j)

theorem good_LG_zero_entry (k : Nat) :
    Good ((G1.LG k,some 0),G1.LBT k) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      have hj:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hj
      have hr:(some (0:Int))=none:=by simpa using congrArg Prod.snd h
      cases hr
    · intro j h
      have hj:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hj
      have hr:(some (0:Int))=some 1:=by simpa using congrArg Prod.snd h
      cases hr
    · intro h
      exact absurd (congrArg Prod.fst h) (G1.LG_ne_base k)
  · constructor
    · intro j h
      have hj:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hj
      rfl
    · constructor
      · intro j r h ha
        exact (G9.good_LG_zero_entry k).2.2 j r h ha
      · intro j r h _
        exact absurd (congrArg Prod.fst h).symm (L_ne_LG j k)

theorem good_G9L_entry (k : Nat) (req : Option Int) (hr : G9.Allowed k req) :
    Good ((G9.L k,req),G9.Val k req) := by
  have hg:=G9.good_L_entry k req hr
  constructor
  · exact hg.1
  · constructor
    · exact hg.2.1
    · constructor
      · exact hg.2.2
      · intro j r h _
        exact absurd (congrArg Prod.fst h).symm (L_ne_G9L j k)

theorem Sound_cons_L (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : Allowed k req) :
    Sound (((L k,req),Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_L_entry k req hr
  · exact hs p h

theorem Sound_cons_LG (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : req=none ∨ req=some 1) :
    Sound (((G1.LG k,req),G1.Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_LG_entry k req hr
  · exact hs p h

theorem Sound_cons_base (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    Sound (((G1.Base,(none:Option Int)),Trans.Dict.BT.zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_base_entry
  · exact hs p h

theorem Sound_cons_LG_zero (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat) :
    Sound (((G1.LG k,some 0),G1.LBT k)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_LG_zero_entry k
  · exact hs p h

theorem Sound_cons_G9L (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : G9.Allowed k req) :
    Sound (((G9.L k,req),G9.Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_G9L_entry k req hr
  · exact hs p h

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun z=>z.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h),?_⟩
  have hb:p.1==key:=List.find?_some (p:=fun z=>z.1==key) (a:=p) h
  exact eq_of_beq hb

theorem value_L_of_good {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (hg : Good p) (k : Nat) (req : Option Int) (hr : Allowed k req)
    (he : p.1=(L k,req)) : p.2=Val k req := hg.2.2.2 k req he hr

theorem value_G9L_of_good {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (hg : Good p) (k : Nat) (req : Option Int) (hr : G9.Allowed k req)
    (he : p.1=(G9.L k,req)) : p.2=G9.Val k req := hg.2.2.1 k req he hr

theorem run_base_ok (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).1=Trans.Dict.BT.zero ∧
      Sound ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).2 := by
  cases hf:tbl.find? (fun z=>z.1==(G1.Base,(none:Option Int))) with
  | some p =>
    rw [G1.run_hit f G1.Base none tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨hg.1.2.2 he,hs⟩
  | none =>
    rw [G1.run_base f tbl hf]
    exact ⟨rfl,Sound_cons_base tbl hs⟩

theorem runAux_LG0 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 1) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) (G1.LG 0) req).run tbl).1=G1.Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+2) (G1.LG 0) req).run tbl).2 := by
  cases hf:tbl.find? (fun z=>z.1==(G1.LG 0,req)) with
  | some p =>
    rw [show g+2=(g+1)+1 by omega,G1.run_hit (g+1) (G1.LG 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h; exact hg.1.1 0 he
    · subst h; exact hg.1.2.1 0 he
  | none =>
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,G1.isReducedP_LG 0,G1.isPrincipalP_LG 0,
      Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG 0,
      show (((0:Nat):Int)+2-1==0)=false from by decide,
      show Trans.Recal.predP (G1.LG 0)=G1.Base from rfl]
    cases hrun:(Trans.Recal.runAux (g+1) G1.Base none) tbl with
    | mk a s =>
      have ih:=run_base_ok g tbl hs
      rw [show (Trans.Recal.runAux (g+1) G1.Base none).run tbl=(a,s) from hrun] at ih
      have ha:a=Trans.Dict.BT.zero:=ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,if_true]
      rcases hr with h|h
      · subst h; exact ⟨rfl,Sound_cons_LG s hsm 0 none (Or.inl rfl)⟩
      · subst h; exact ⟨rfl,Sound_cons_LG s hsm 0 (some 1) (Or.inr rfl)⟩

theorem runAux_LG : ∀ (k g : Nat) (req : Option Int),
    req=none ∨ req=some 1 → ∀ tbl : Trans.Recal.Memo, Sound tbl →
      ((Trans.Recal.runAux (k+g+2) (G1.LG k) req).run tbl).1=G1.Val k req ∧
        Sound ((Trans.Recal.runAux (k+g+2) (G1.LG k) req).run tbl).2
  | 0,g,req,hr,tbl,hs => runAux_LG0 g req hr tbl hs
  | k+1,g,req,hr,tbl,hs => by
    cases hf:tbl.find? (fun z=>z.1==(G1.LG (k+1),req)) with
    | some p =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,
        G1.run_hit (k+g+2) (G1.LG (k+1)) req tbl p hf]
      obtain ⟨hg,he⟩:=good_of_find hs hf
      refine ⟨?_,hs⟩
      rcases hr with h|h
      · subst h; exact hg.1.1 (k+1) he
      · subst h; exact hg.1.2.1 (k+1) he
    | none =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,Trans.Recal.runAux]
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hf,G1.isReducedP_LG (k+1),G1.isPrincipalP_LG (k+1),
        Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG (k+1),
        show ((((k+1:Nat):Int)+2-1)==0)=false from by simp; omega,
        G1.predP_LG k]
      cases hrun:(Trans.Recal.runAux (k+g+2) (G1.LG k) none) tbl with
      | mk a s =>
        have ih1:=runAux_LG k g none (Or.inl rfl) tbl hs
        rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) none).run tbl=(a,s)
          from hrun] at ih1
        have ha:a=G1.LBT k:=ih1.1
        have hsm:Sound s:=ih1.2
        subst ha
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,
          show ((G1.LBT k)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (G1.LG (k+1)) 0 (((k+1:Nat):Int)+2-1) 0=1 from
            G1.fpar_LG_0_e (k+1) (((k+1:Nat):Int)+2-1) (by push_cast; omega)
              (by push_cast; omega),G1.adm_LG_1 (k+1)]
        cases hrun2:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)) s with
        | mk c1 s2 =>
          have ih2:=runAux_LG k g (some 1) (Or.inr rfl) s hsm
          rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)).run s=(c1,s2)
            from hrun2] at ih2
          have hc1:c1=Trans.Dict.BT.D 1 (G1.rep1 k):=ih2.1
          have hsm2:Sound s2:=ih2.2
          subst hc1
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run,
            show Trans.Recal.transTypeMain (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1)=3 from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.transType_LG k,
            show Trans.Recal.mkC2 (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1) 3
                (.D 1 (G1.rep1 k))=.D 1 (G1.rep1 (k+1)) from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.mkC2_LG k]
          rcases hr with h|h
          · subst h
            rw [G1.replMark_LG ((G1.LBT k).size+
              ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                (Trans.Dict.BT.D 1 (G1.rep1 (k+1))).size+4)) k (by omega)]
            simp only [Option.getD_some]
            exact ⟨rfl,Sound_cons_LG s2 hsm2 (k+1) none (Or.inl rfl)⟩
          · subst h
            simp only [show ((1:Int)<((k+1:Nat):Int)+2-1) by push_cast; omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)) s2 with
            | mk c0 s3 =>
              have ih3:=runAux_LG k g (some 1) (Or.inr rfl) s2 hsm2
              rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)).run s2=(c0,s3)
                from hrun3] at ih3
              have hc0:c0=.D 1 (G1.rep1 k):=ih3.1
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self (.D 1 (G1.rep1 k))),
                G1.replMark_self ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                  ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                    (Trans.Dict.BT.D 1 (G1.rep1 (k+1))).size+4))
                  1 (G1.rep1 k) (.D 1 (G1.rep1 (k+1))) (by omega)]
              simp only [Option.getD_some]
              exact ⟨rfl,Sound_cons_LG s3 hsm3 (k+1) (some 1) (Or.inr rfl)⟩

theorem isMarkedB_LG_inner (k : Nat) :
    Trans.Recal.isMarkedB (G1.LBT k) (.D 1 (G1.rep1 k))=true := by
  unfold Trans.Recal.isMarkedB
  rw [show (G1.LBT k).size+2=
    ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+2)+1 by
      simp only [G1.LBT,Trans.Dict.BT.size]
      omega]
  rw [Trans.Recal.isMarkedBAux]
  rw [show ((G1.LBT k)==(.D 1 (G1.rep1 k)))=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  exact G1.isMarkedB_self (.D 1 (G1.rep1 k))

theorem runAux_LG_zero : ∀ (k g : Nat) (tbl : Trans.Recal.Memo), Sound tbl →
    ((Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)).run tbl).1=G1.LBT k ∧
      Sound ((Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)).run tbl).2
  | 0,g,tbl,hs => by
    simp only [Nat.zero_add]
    cases hf:tbl.find? (fun z=>z.1==(G1.LG 0,some 0)) with
    | some p =>
      rw [show g+2=(g+1)+1 by omega,G1.run_hit (g+1) (G1.LG 0) (some 0) tbl p hf]
      obtain ⟨hg,he⟩:=good_of_find hs hf
      exact ⟨hg.2.1 0 he,hs⟩
    | none =>
      rw [show g+2=(g+1)+1 by omega,Trans.Recal.runAux]
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hf,G1.isReducedP_LG 0,G1.isPrincipalP_LG 0,
        Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG 0,
        show (((0:Nat):Int)+2-1==0)=false from by decide,
        show Trans.Recal.predP (G1.LG 0)=G1.Base from rfl]
      cases hrun:(Trans.Recal.runAux (g+1) G1.Base none) tbl with
      | mk a s =>
        have ih:=run_base_ok g tbl hs
        rw [show (Trans.Recal.runAux (g+1) G1.Base none).run tbl=(a,s) from hrun] at ih
        have ha:a=Trans.Dict.BT.zero:=ih.1
        have hsm:Sound s:=ih.2
        subst ha
        simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,
          if_true,show ((0:Int)==0)=true from rfl]
        exact ⟨rfl,Sound_cons_LG_zero s hsm 0⟩
  | k+1,g,tbl,hs => by
    cases hf:tbl.find? (fun z=>z.1==(G1.LG (k+1),some 0)) with
    | some p =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,
        G1.run_hit (k+g+2) (G1.LG (k+1)) (some 0) tbl p hf]
      obtain ⟨hg,he⟩:=good_of_find hs hf
      exact ⟨hg.2.1 (k+1) he,hs⟩
    | none =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,Trans.Recal.runAux]
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hf,G1.isReducedP_LG (k+1),G1.isPrincipalP_LG (k+1),
        Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG (k+1),
        show ((((k+1:Nat):Int)+2-1)==0)=false from by simp; omega,G1.predP_LG k]
      cases hrun:(Trans.Recal.runAux (k+g+2) (G1.LG k) none) tbl with
      | mk a s =>
        have ih1:=runAux_LG k g none (Or.inl rfl) tbl hs
        rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) none).run tbl=(a,s)
          from hrun] at ih1
        have ha:a=G1.LBT k:=ih1.1
        have hsm:Sound s:=ih1.2
        subst ha
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,
          show ((G1.LBT k)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (G1.LG (k+1)) 0 (((k+1:Nat):Int)+2-1) 0=1 from
            G1.fpar_LG_0_e (k+1) (((k+1:Nat):Int)+2-1) (by push_cast; omega)
              (by push_cast; omega),G1.adm_LG_1 (k+1)]
        cases hrun2:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)) s with
        | mk c1 s2 =>
          have ih2:=runAux_LG k g (some 1) (Or.inr rfl) s hsm
          rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)).run s=(c1,s2)
            from hrun2] at ih2
          have hc1:c1=.D 1 (G1.rep1 k):=ih2.1
          have hsm2:Sound s2:=ih2.2
          subst hc1
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run,
            show Trans.Recal.transTypeMain (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1)=3 from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.transType_LG k,
            show Trans.Recal.mkC2 (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1) 3
                (.D 1 (G1.rep1 k))=.D 1 (G1.rep1 (k+1)) from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.mkC2_LG k,
            show ((0:Int)<((k+1:Nat):Int)+2-1) by push_cast; omega,if_true]
          cases hrun3:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)) s2 with
          | mk c0 s3 =>
            have ih3:=runAux_LG_zero k g s2 hsm2
            rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0:c0=G1.LBT k:=ih3.1
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (isMarkedB_LG_inner k),
              G1.replMark_LG ((G1.LBT k).size+
                ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                  (Trans.Dict.BT.D 1 (G1.rep1 (k+1))).size+4)) k (by omega)]
            simp only [Option.getD_some]
            exact ⟨by trivial,Sound_cons_LG_zero s3 hsm3 (k+1)⟩

set_option maxHeartbeats 2000000 in
theorem runAux_G9L0 (g : Nat) (req : Option Int) (hr : G9.Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+5) (G9.L 0) req).run tbl).1=G9.Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+5) (G9.L 0) req).run tbl).2 := by
  have hr' : req=none ∨ req=some 0 := by
    rw [G9.Allowed,if_pos (by decide)] at hr
    simpa using hr
  cases hf:tbl.find? (fun z=>z.1==(G9.L 0,req)) with
  | some p =>
    rw [show g+5=(g+4)+1 by omega,G1.run_hit (g+4) (G9.L 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_G9L_of_good hg 0 req hr he,hs⟩
  | none =>
    rw [show g+5=(g+4)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,G9.isReducedP_L 0,G9.isPrincipalP_L 0,
      Bool.not_true,Bool.false_eq_true,if_false,G9.lenI_L 0,
      show (((0:Int)+5-1)==0)=false from by decide,
      show Trans.Recal.predP (G9.L 0)=G1.LG 2 from rfl]
    cases hrun:(Trans.Recal.runAux (g+4) (G1.LG 2) none) tbl with
    | mk t1 s =>
      have ih1:=runAux_LG 2 g none (Or.inl rfl) tbl hs
      rw [show 2+g+2=g+4 by omega] at ih1
      rw [show (Trans.Recal.runAux (g+4) (G1.LG 2) none).run tbl=(t1,s)
        from hrun] at ih1
      have ht1:t1=G1.LBT 2:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux (g+4) (G1.LG 2) (some 1)) s with
      | mk c1 s2 =>
        have ih2:=runAux_LG 2 g (some 1) (Or.inr rfl) s hsm
        rw [show 2+g+2=g+4 by omega] at ih2
        rw [show (Trans.Recal.runAux (g+4) (G1.LG 2) (some 1)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=D1ss:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((0:Nat):Int)+5-1)=4 by omega,
          show ((4:Int)==0)=false from rfl,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((G1.LBT 2)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (G9.L 0) 0 4 0=1 from rfl,G9.adm_L_zero,
          hrun2,G9.transType_L_zero,G9.mkC2_L_zero]
        rcases hr' with h|h
        · subst h
          rw [G9.repl_L_zero _ (by omega)]
          simp only [Option.getD_some]
          refine ⟨G9.Val_none 0,?_⟩
          have ht:=Sound_cons_G9L s2 hsm2 0 none (G9.Allowed_none 0)
          rw [G9.Val_none] at ht
          exact ht
        · subst h
          simp only [show ((0:Int)<4) by omega,if_true]
          cases hrun3:(Trans.Recal.runAux (g+4) (G1.LG 2) (some 0)) s2 with
          | mk c0 s3 =>
            have ih3:=runAux_LG_zero 2 g s2 hsm2
            rw [show 2+g+2=g+4 by omega] at ih3
            rw [show (Trans.Recal.runAux (g+4) (G1.LG 2) (some 0)).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0:c0=G1.LBT 2:=ih3.1
            have hsm3:Sound s3:=ih3.2
            subst hc0
            simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run,hrun3]
            have hm : Trans.Recal.isMarkedB (G1.LBT 2) D1ss=true :=
              isMarkedB_LG_inner 2
            rw [if_pos hm,G9.repl_L_zero _ (by omega)]
            simp only [Option.getD_some]
            refine ⟨(G9.Val_phase0 0).symm,?_⟩
            exact Sound_cons_G9L s3 hsm3 0 (some 0) (G9.Allowed_phase0 0)

theorem adm_L_zero : Trans.Recal.adm (L 0) 0=0 := by rfl
theorem transType_L_zero : Trans.Recal.transTypeMain (L 0) 0 5=5 := by rfl
theorem mkC2_L_zero :
    Trans.Recal.mkC2 (L 0) 0 5 5 Anchor=.D 0 (Part 0) := by rfl

theorem repl_L_zero (f : Nat) (hf : 1≤f) :
    Trans.Recal.replMark f (G9.LBT 0) Anchor (.D 0 (Part 0))=some (LBT 0) := by
  change Trans.Recal.replMark f (.D 0 A0) (.D 0 A0) (.D 0 (Part 0))=
    some (.D 0 (Part 0))
  exact G1.replMark_self f 0 A0 (.D 0 (Part 0)) hf

theorem repl_D0_D1_self (f : Nat) (a cc : Trans.Dict.BT) (hf : 2≤f) :
    Trans.Recal.replMark f (.D 0 (.D 1 a)) (.D 1 a) cc=
      some (.D 0 cc) := by
  obtain ⟨g,rfl⟩ : ∃ g,f=g+2:=⟨f-2,by omega⟩
  rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
  rw [show ((Trans.Dict.BT.D 0 (.D 1 a))==(.D 1 a))=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [G1.replMark_self (g+1) 1 a cc (by omega)]
  rfl

set_option maxHeartbeats 2000000 in
theorem runAux_L0 (g : Nat) (req : Option Int) (hr : Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+6) (L 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+6) (L 0) req).run tbl).2 := by
  have hr' : req=none ∨ req=some 5 := by
    rw [Allowed,if_pos (by decide)] at hr
    simpa using hr
  cases hf:tbl.find? (fun z=>z.1==(L 0,req)) with
  | some p =>
    rw [show g+6=(g+5)+1 by omega,G1.run_hit (g+5) (L 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg 0 req hr he,hs⟩
  | none =>
    rw [show g+6=(g+5)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L 0,isPrincipalP_L 0,
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L 0,
      show (((0:Int)+6-1)==0)=false from by decide,
      show Trans.Recal.predP (L 0)=G9.L 0 from rfl]
    cases hrun:(Trans.Recal.runAux (g+5) (G9.L 0) none) tbl with
    | mk t1 s =>
      have ih1:=runAux_G9L0 g none (G9.Allowed_none 0) tbl hs
      rw [show (Trans.Recal.runAux (g+5) (G9.L 0) none).run tbl=(t1,s)
        from hrun] at ih1
      have ht1:t1=G9.LBT 0:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux (g+5) (G9.L 0) (some 0)) s with
      | mk c1 s2 =>
        have ih2:=runAux_G9L0 g (some 0) (G9.Allowed_phase0 0) s hsm
        rw [show (Trans.Recal.runAux (g+5) (G9.L 0) (some 0)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=Anchor:=by simpa only [G9.Val_phase0 0] using ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((0:Nat):Int)+6-1)=5 by omega,
          show ((5:Int)==0)=false from rfl,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((G9.LBT 0)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (L 0) 0 5 0=0 from rfl,adm_L_zero,
          hrun2,transType_L_zero,mkC2_L_zero]
        rcases hr' with h|h
        · subst h
          rw [repl_L_zero _ (by omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none 0,?_⟩
          have ht:=Sound_cons_L s2 hsm2 0 none (Allowed_none 0)
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬((5:Int)<5) by omega,if_false]
          refine ⟨(Val_phase0 0).symm,?_⟩
          exact Sound_cons_L s2 hsm2 0 (some 5) (Allowed_phase0 0)

theorem size_W (n : Nat) (b : Trans.Dict.BT) :
    (W n b).size=12*n+b.size := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    simp only [W,Trans.Dict.BT.size,ih]
    omega

set_option maxHeartbeats 2000000 in
theorem runAux_phase0_step (a g : Nat) (req : Option Int)
    (hr : Allowed (6*a+1) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (6*a) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux (6*a+g+6) (L (6*a)) r).run s).1=Val (6*a) r ∧
          Sound ((Trans.Recal.runAux (6*a+g+6) (L (6*a)) r).run s).2) :
    ((Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1)) req).run tbl).1=
        Val (6*a+1) req ∧
      Sound ((Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((6*a+6:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_pos (by omega)] at hr
    simpa only [show 6*a+1+5=6*a+6 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (6*a+1),req)) with
  | some p =>
    rw [show (6*a+1)+g+6=(6*a+g+6)+1 by omega,
      G1.run_hit (6*a+g+6) (L (6*a+1)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (6*a+1) req hr he,hs⟩
  | none =>
    rw [show (6*a+1)+g+6=(6*a+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (6*a+1),isPrincipalP_L (6*a+1),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (6*a+1),
      show ((((6*a+1:Nat):Int)+6-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (6*a+1))=L (6*a) from by
        simpa only [show 6*a+1=6*a+1 by rfl] using predP_L (6*a)]
    cases hrun:(Trans.Recal.runAux (6*a+g+6) (L (6*a)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (6*a)) tbl hs
      rw [show (Trans.Recal.runAux (6*a+g+6) (L (6*a)) none).run tbl=(t1,s)
        from hrun] at ih1
      have ht1:t1=LBT (6*a):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux (6*a+g+6) (L (6*a))
          (some ((6*a+5:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((6*a+5:Nat):Int)) (Allowed_phase0 a) s hsm
        rw [show (Trans.Recal.runAux (6*a+g+6) (L (6*a))
          (some ((6*a+5:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1z:=ih2.1.trans (Val_phase0 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((6*a+1:Nat):Int)+6-1)=((6*a+6:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (6*a))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase0]; rfl,
          Bool.false_eq_true,if_false,j0_L_new1,adm_L_new1,hrun2,
          transType_L_new1,mkC2_L_new1]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase0 a _ (by
            rw [LBT_phase0]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (6*a+1),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (6*a+1) none (Allowed_none (6*a+1))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬(((6*a+6:Nat):Int)<((6*a+6:Nat):Int)) by omega,
            if_false,gp1_L_phase0_tail a (6*a+1) (by omega),
            StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          refine ⟨(Val_phase1 a).symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 (6*a+1) (some ((6*a+6:Nat):Int))
            (Allowed_phase1 a)
          rw [Val_phase1] at ht
          exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase1_step (a g : Nat) (req : Option Int)
    (hr : Allowed (6*a+2) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (6*a+1) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1)) r).run s).1=
            Val (6*a+1) r ∧
          Sound ((Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1)) r).run s).2) :
    ((Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2)) req).run tbl).1=
        Val (6*a+2) req ∧
      Sound ((Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((6*a+6:Nat):Int) ∨
      req=some ((6*a+7:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_neg (by omega),if_pos (by omega)] at hr
    simpa only [show 6*a+2+4=6*a+6 by omega,
      show 6*a+2+5=6*a+7 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (6*a+2),req)) with
  | some p =>
    rw [show (6*a+2)+g+6=((6*a+1)+g+6)+1 by omega,
      G1.run_hit ((6*a+1)+g+6) (L (6*a+2)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (6*a+2) req hr he,hs⟩
  | none =>
    rw [show (6*a+2)+g+6=((6*a+1)+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (6*a+2),isPrincipalP_L (6*a+2),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (6*a+2),
      show ((((6*a+2:Nat):Int)+6-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (6*a+2))=L (6*a+1) from by
        simpa only [show 6*a+2=(6*a+1)+1 by omega] using predP_L (6*a+1)]
    cases hrun:(Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (6*a+1)) tbl hs
      rw [show (Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (6*a+1):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1))
          (some ((6*a+6:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((6*a+6:Nat):Int)) (Allowed_phase1 a) s hsm
        rw [show (Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1))
          (some ((6*a+6:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D0z:=ih2.1.trans (Val_phase1 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((6*a+2:Nat):Int)+6-1)=((6*a+7:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (6*a+1))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase1]; rfl,
          Bool.false_eq_true,if_false,j0_L_new2,adm_L_new2,hrun2,
          transType_L_new2,mkC2_L_new2]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase1 a _ (by
            rw [LBT_phase1]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (6*a+2),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (6*a+2) none (Allowed_none (6*a+2))
          rw [Val_none] at ht
          exact ht
        · rcases h with h|h
          · subst h
            simp only [show (((6*a+6:Nat):Int)<((6*a+7:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1))
                (some ((6*a+6:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((6*a+6:Nat):Int)) (Allowed_phase1 a) s2 hsm2
              rw [show (Trans.Recal.runAux ((6*a+1)+g+6) (L (6*a+1))
                (some ((6*a+6:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=D0z:=ih3.1.trans (Val_phase1 a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self D0z),
                G1.replMark_self (D0z.size+(D0z.size+(Trans.Dict.BT.D 0 D1z).size+4))
                  0 .zero (.D 0 D1z) (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase2carry a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (6*a+2) (some ((6*a+6:Nat):Int))
                (Allowed_phase2carry a)
              rw [Val_phase2carry] at ht
              exact ht
          · subst h
            simp only [show ¬(((6*a+7:Nat):Int)<((6*a+7:Nat):Int)) by omega,
              if_false,gp1_L_phase1_tail a (6*a+2) (by omega),
              StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            refine ⟨(Val_phase2 a).symm,?_⟩
            have ht:=Sound_cons_L s2 hsm2 (6*a+2) (some ((6*a+7:Nat):Int))
              (Allowed_phase2 a)
            rw [Val_phase2] at ht
            exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase2_step (a g : Nat) (req : Option Int)
    (hr : Allowed (6*a+3) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (6*a+2) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2)) r).run s).1=
            Val (6*a+2) r ∧
          Sound ((Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2)) r).run s).2) :
    ((Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3)) req).run tbl).1=
        Val (6*a+3) req ∧
      Sound ((Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((6*a+6:Nat):Int) ∨
      req=some ((6*a+7:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_pos (by omega)] at hr
    simpa only [show 6*a+3+3=6*a+6 by omega,
      show 6*a+3+4=6*a+7 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (6*a+3),req)) with
  | some p =>
    rw [show (6*a+3)+g+6=((6*a+2)+g+6)+1 by omega,
      G1.run_hit ((6*a+2)+g+6) (L (6*a+3)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (6*a+3) req hr he,hs⟩
  | none =>
    rw [show (6*a+3)+g+6=((6*a+2)+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (6*a+3),isPrincipalP_L (6*a+3),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (6*a+3),
      show ((((6*a+3:Nat):Int)+6-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (6*a+3))=L (6*a+2) from by
        simpa only [show 6*a+3=(6*a+2)+1 by omega] using predP_L (6*a+2)]
    cases hrun:(Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (6*a+2)) tbl hs
      rw [show (Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (6*a+2):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2))
          (some ((6*a+7:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((6*a+7:Nat):Int)) (Allowed_phase2 a) s hsm
        rw [show (Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2))
          (some ((6*a+7:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1z:=ih2.1.trans (Val_phase2 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((6*a+3:Nat):Int)+6-1)=((6*a+8:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (6*a+2))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase2]; rfl,
          Bool.false_eq_true,if_false,j0_L_new3,adm_L_new3,hrun2,
          transType_L_new3,mkC2_L_new3]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase2 a _ (by
            rw [LBT_phase2]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (6*a+3),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (6*a+3) none (Allowed_none (6*a+3))
          rw [Val_none] at ht
          exact ht
        · rcases h with h|h
          · subst h
            simp only [show (((6*a+6:Nat):Int)<((6*a+8:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2))
                (some ((6*a+6:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((6*a+6:Nat):Int)) (Allowed_phase2carry a) s2 hsm2
              rw [show (Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2))
                (some ((6*a+6:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=.D 0 D1z:=ih3.1.trans (Val_phase2carry a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              have hm : Trans.Recal.isMarkedB (.D 0 D1z) D1z=true := by
                exact isMarkedB_LG_inner 0
              rw [if_pos hm,repl_D0_D1_self _ .zero D11z (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase3carry a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (6*a+3) (some ((6*a+6:Nat):Int))
                (Allowed_phase3carry a)
              rw [Val_phase3carry] at ht
              exact ht
          · subst h
            simp only [show (((6*a+7:Nat):Int)<((6*a+8:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2))
                (some ((6*a+7:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((6*a+7:Nat):Int)) (Allowed_phase2 a) s2 hsm2
              rw [show (Trans.Recal.runAux ((6*a+2)+g+6) (L (6*a+2))
                (some ((6*a+7:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=D1z:=ih3.1.trans (Val_phase2 a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self D1z),
                G1.replMark_self (D1z.size+(D1z.size+D11z.size+4))
                  1 .zero D11z (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase3 a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (6*a+3) (some ((6*a+7:Nat):Int))
                (Allowed_phase3 a)
              rw [Val_phase3] at ht
              exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase3_step (a g : Nat) (req : Option Int)
    (hr : Allowed (6*a+4) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (6*a+3) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3)) r).run s).1=
            Val (6*a+3) r ∧
          Sound ((Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3)) r).run s).2) :
    ((Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4)) req).run tbl).1=
        Val (6*a+4) req ∧
      Sound ((Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((6*a+6:Nat):Int) ∨
      req=some ((6*a+7:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega),if_pos (by omega)] at hr
    simpa only [show 6*a+4+2=6*a+6 by omega,
      show 6*a+4+3=6*a+7 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (6*a+4),req)) with
  | some p =>
    rw [show (6*a+4)+g+6=((6*a+3)+g+6)+1 by omega,
      G1.run_hit ((6*a+3)+g+6) (L (6*a+4)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (6*a+4) req hr he,hs⟩
  | none =>
    rw [show (6*a+4)+g+6=((6*a+3)+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (6*a+4),isPrincipalP_L (6*a+4),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (6*a+4),
      show ((((6*a+4:Nat):Int)+6-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (6*a+4))=L (6*a+3) from by
        simpa only [show 6*a+4=(6*a+3)+1 by omega] using predP_L (6*a+3)]
    cases hrun:(Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (6*a+3)) tbl hs
      rw [show (Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (6*a+3):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3))
          (some ((6*a+7:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((6*a+7:Nat):Int)) (Allowed_phase3 a) s hsm
        rw [show (Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3))
          (some ((6*a+7:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D11z:=ih2.1.trans (Val_phase3 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((6*a+4:Nat):Int)+6-1)=((6*a+9:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (6*a+3))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase3]; rfl,
          Bool.false_eq_true,if_false,j0_L_new4,adm_L_new4,hrun2,
          transType_L_new4,mkC2_L_new4]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase3 a _ (by
            rw [LBT_phase3]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (6*a+4),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (6*a+4) none (Allowed_none (6*a+4))
          rw [Val_none] at ht
          exact ht
        · rcases h with h|h
          · subst h
            simp only [show (((6*a+6:Nat):Int)<((6*a+9:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3))
                (some ((6*a+6:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((6*a+6:Nat):Int)) (Allowed_phase3carry a) s2 hsm2
              rw [show (Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3))
                (some ((6*a+6:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=.D 0 D11z:=ih3.1.trans (Val_phase3carry a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              have hm : Trans.Recal.isMarkedB (.D 0 D11z) D11z=true := by
                exact isMarkedB_LG_inner 1
              rw [if_pos hm,repl_D0_D1_self _ D1z D1ss (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase4carry a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (6*a+4) (some ((6*a+6:Nat):Int))
                (Allowed_phase4carry a)
              rw [Val_phase4carry] at ht
              exact ht
          · subst h
            simp only [show (((6*a+7:Nat):Int)<((6*a+9:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3))
                (some ((6*a+7:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((6*a+7:Nat):Int)) (Allowed_phase3 a) s2 hsm2
              rw [show (Trans.Recal.runAux ((6*a+3)+g+6) (L (6*a+3))
                (some ((6*a+7:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=D11z:=ih3.1.trans (Val_phase3 a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self D11z),
                G1.replMark_self (D11z.size+(D11z.size+D1ss.size+4))
                  1 D1z D1ss (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase4 a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (6*a+4) (some ((6*a+7:Nat):Int))
                (Allowed_phase4 a)
              rw [Val_phase4] at ht
              exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase4_step (a g : Nat) (req : Option Int)
    (hr : Allowed (6*a+5) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (6*a+4) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4)) r).run s).1=
            Val (6*a+4) r ∧
          Sound ((Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4)) r).run s).2) :
    ((Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5)) req).run tbl).1=
        Val (6*a+5) req ∧
      Sound ((Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((6*a+6:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega),if_neg (by omega)] at hr
    simpa only [show 6*a+5+1=6*a+6 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (6*a+5),req)) with
  | some p =>
    rw [show (6*a+5)+g+6=((6*a+4)+g+6)+1 by omega,
      G1.run_hit ((6*a+4)+g+6) (L (6*a+5)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (6*a+5) req hr he,hs⟩
  | none =>
    rw [show (6*a+5)+g+6=((6*a+4)+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (6*a+5),isPrincipalP_L (6*a+5),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (6*a+5),
      show ((((6*a+5:Nat):Int)+6-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (6*a+5))=L (6*a+4) from by
        simpa only [show 6*a+5=(6*a+4)+1 by omega] using predP_L (6*a+4)]
    cases hrun:(Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (6*a+4)) tbl hs
      rw [show (Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (6*a+4):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4))
          (some ((6*a+7:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((6*a+7:Nat):Int)) (Allowed_phase4 a) s hsm
        rw [show (Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4))
          (some ((6*a+7:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1ss:=ih2.1.trans (Val_phase4 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((6*a+5:Nat):Int)+6-1)=((6*a+10:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (6*a+4))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase4]; rfl,
          Bool.false_eq_true,if_false,j0_L_new5,adm_L_new5,hrun2,
          transType_L_new5,mkC2_L_new5]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase4 a _ (by
            rw [LBT_phase4]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (6*a+5),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (6*a+5) none (Allowed_none (6*a+5))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show (((6*a+6:Nat):Int)<((6*a+10:Nat):Int)) by omega,
            if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          cases hrun3:(Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4))
              (some ((6*a+6:Nat):Int))) s2 with
          | mk c0 s3 =>
            have ih3:=ih (some ((6*a+6:Nat):Int)) (Allowed_phase4carry a) s2 hsm2
            rw [show (Trans.Recal.runAux ((6*a+4)+g+6) (L (6*a+4))
              (some ((6*a+6:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
            have hc0:c0=.D 0 D1ss:=ih3.1.trans (Val_phase4carry a)
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            have hm : Trans.Recal.isMarkedB (.D 0 D1ss) D1ss=true := by
              show Trans.Recal.isMarkedB (G1.LBT 2) (.D 1 (G1.rep1 2))=true
              exact isMarkedB_LG_inner 2
            rw [if_pos hm,repl_D0_D1_self _ (.sum D1z D1z) A0 (by omega)]
            simp only [Option.getD_some]
            refine ⟨(Val_phase5 a).symm,?_⟩
            have ht:=Sound_cons_L s3 hsm3 (6*a+5) (some ((6*a+6:Nat):Int))
              (Allowed_phase5 a)
            rw [Val_phase5] at ht
            exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase5_step (a g : Nat) (req : Option Int)
    (hr : Allowed (6*a+6) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (6*a+5) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5)) r).run s).1=
            Val (6*a+5) r ∧
          Sound ((Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5)) r).run s).2) :
    ((Trans.Recal.runAux ((6*a+6)+g+6) (L (6*a+6)) req).run tbl).1=
        Val (6*a+6) req ∧
      Sound ((Trans.Recal.runAux ((6*a+6)+g+6) (L (6*a+6)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((6*a+11:Nat):Int) := by
    rw [Allowed,if_pos (by omega)] at hr
    simpa only [show 6*a+6+5=6*a+11 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (6*a+6),req)) with
  | some p =>
    rw [show (6*a+6)+g+6=((6*a+5)+g+6)+1 by omega,
      G1.run_hit ((6*a+5)+g+6) (L (6*a+6)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (6*a+6) req hr he,hs⟩
  | none =>
    rw [show (6*a+6)+g+6=((6*a+5)+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (6*a+6),isPrincipalP_L (6*a+6),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (6*a+6),
      show ((((6*a+6:Nat):Int)+6-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (6*a+6))=L (6*a+5) from by
        simpa only [show 6*a+6=(6*a+5)+1 by omega] using predP_L (6*a+5)]
    cases hrun:(Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (6*a+5)) tbl hs
      rw [show (Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (6*a+5):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5))
          (some ((6*a+6:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((6*a+6:Nat):Int)) (Allowed_phase5 a) s hsm
        rw [show (Trans.Recal.runAux ((6*a+5)+g+6) (L (6*a+5))
          (some ((6*a+6:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=Anchor:=ih2.1.trans (Val_phase5 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((6*a+6:Nat):Int)+6-1)=((6*a+11:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (6*a+5))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase5]; rfl,
          Bool.false_eq_true,if_false,j0_L_new6,adm_L_new6,hrun2,
          transType_L_new6,mkC2_L_new6]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase5 a _ (by
            rw [LBT_phase5]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (6*a+6),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (6*a+6) none (Allowed_none (6*a+6))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬(((6*a+11:Nat):Int)<((6*a+11:Nat):Int)) by omega,
            if_false,gp1_L_phase5_tail a (6*a+6) (by omega),
            StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          have hv : Val (6*a+6) (some ((6*a+11:Nat):Int))=D1z := by
            simpa only [show 6*(a+1)=6*a+6 by omega,
              show 6*(a+1)+5=6*a+11 by omega] using Val_phase0 (a+1)
          refine ⟨hv.symm,?_⟩
          have ha : Allowed (6*a+6) (some ((6*a+11:Nat):Int)) := by
            simpa only [show 6*(a+1)=6*a+6 by omega,
              show 6*(a+1)+5=6*a+11 by omega] using Allowed_phase0 (a+1)
          have ht:=Sound_cons_L s2 hsm2 (6*a+6) (some ((6*a+11:Nat):Int)) ha
          rw [hv] at ht
          exact ht

def RunOK (k : Nat) : Prop :=
  ∀ g : Nat, ∀ req : Option Int, Allowed k req →
    ∀ tbl : Trans.Recal.Memo, Sound tbl →
      ((Trans.Recal.runAux (k+g+6) (L k) req).run tbl).1=Val k req ∧
        Sound ((Trans.Recal.runAux (k+g+6) (L k) req).run tbl).2

theorem runOK_zero : RunOK 0 := by
  intro g req hr tbl hs
  simpa only [Nat.zero_add] using runAux_L0 g req hr tbl hs

theorem runOK_phase0 (a : Nat) (ih : RunOK (6*a)) : RunOK (6*a+1) := by
  intro g req hr tbl hs
  exact runAux_phase0_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase1 (a : Nat) (ih : RunOK (6*a+1)) : RunOK (6*a+2) := by
  intro g req hr tbl hs
  exact runAux_phase1_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase2 (a : Nat) (ih : RunOK (6*a+2)) : RunOK (6*a+3) := by
  intro g req hr tbl hs
  exact runAux_phase2_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase3 (a : Nat) (ih : RunOK (6*a+3)) : RunOK (6*a+4) := by
  intro g req hr tbl hs
  exact runAux_phase3_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase4 (a : Nat) (ih : RunOK (6*a+4)) : RunOK (6*a+5) := by
  intro g req hr tbl hs
  exact runAux_phase4_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase5 (a : Nat) (ih : RunOK (6*a+5)) : RunOK (6*a+6) := by
  intro g req hr tbl hs
  exact runAux_phase5_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_sextuple (a : Nat) :
    RunOK (6*a) ∧ RunOK (6*a+1) ∧ RunOK (6*a+2) ∧
      RunOK (6*a+3) ∧ RunOK (6*a+4) ∧ RunOK (6*a+5) := by
  induction a with
  | zero =>
    have h0 : RunOK (6*0) := by simpa only using runOK_zero
    have h1:=runOK_phase0 0 h0
    have h2:=runOK_phase1 0 h1
    have h3:=runOK_phase2 0 h2
    have h4:=runOK_phase3 0 h3
    exact ⟨h0,h1,h2,h3,h4,runOK_phase4 0 h4⟩
  | succ a ih =>
    have h5:=runOK_phase4 a ih.2.2.2.2.1
    have h0' := runOK_phase5 a h5
    have h0 : RunOK (6*(a+1)) := by
      simpa only [show 6*(a+1)=6*a+6 by omega] using h0'
    have h1:=runOK_phase0 (a+1) h0
    have h2:=runOK_phase1 (a+1) h1
    have h3:=runOK_phase2 (a+1) h2
    have h4:=runOK_phase3 (a+1) h3
    exact ⟨h0,h1,h2,h3,h4,runOK_phase4 (a+1) h4⟩

set_option maxHeartbeats 2000000 in
theorem runAux_L (k g : Nat) (req : Option Int) (hr : Allowed k req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+6) (L k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+6) (L k) req).run tbl).2 := by
  have hk : RunOK k := by
    have hm : k%6=0 ∨ k%6=1 ∨ k%6=2 ∨ k%6=3 ∨ k%6=4 ∨ k%6=5 := by omega
    have hdiv:=Nat.mod_add_div k 6
    rcases hm with h0|h1|h2|h3|h4|h5
    · have heq:k=6*(k/6):=by omega
      rw [heq]
      exact (runOK_sextuple (k/6)).1
    · have heq:k=6*(k/6)+1:=by omega
      rw [heq]
      exact (runOK_sextuple (k/6)).2.1
    · have heq:k=6*(k/6)+2:=by omega
      rw [heq]
      exact (runOK_sextuple (k/6)).2.2.1
    · have heq:k=6*(k/6)+3:=by omega
      rw [heq]
      exact (runOK_sextuple (k/6)).2.2.2.1
    · have heq:k=6*(k/6)+4:=by omega
      rw [heq]
      exact (runOK_sextuple (k/6)).2.2.2.2.1
    · have heq:k=6*(k/6)+5:=by omega
      rw [heq]
      exact (runOK_sextuple (k/6)).2.2.2.2.2
  exact hk g req hr tbl hs

/-- Link 2: the recalibrated reader follows the entire six-phase ladder. -/
theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m)=LBT m := by
  have hb : m+6≤Trans.Recal.transFuel (L m) := by
    show m+6≤40+6*((L m).length+Trans.Recal.maxE (L m))
    rw [length_L]
    omega
  have h : Trans.Recal.transFuel (L m)=
      m+(Trans.Recal.transFuel (L m)-m-6)+6 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L m)) (L m) none).run []).1=_
  rw [h]
  simpa only [Val_none] using
    (runAux_L m _ none (Allowed_none m) [] Sound_nil).1

/-! ### Link 3: the dictionary and the shifted fundamental sequence. -/

abbrev Z0t : Term := Z zero

/-- The term-side iteration exposed by complete six-column blocks. -/
def Jt : Nat → Term
  | 0 => Bph
  | n+1 => phi one (Jt n)

theorem Jt_cnv : ∀ n : Nat, Evidence.WF.CNV (Jt n)=true
  | 0 => by decide
  | n+1 => by
    show (Evidence.WF.CNV one && Evidence.WF.CNV (Jt n))=true
    rw [Jt_cnv n]
    rfl

theorem Jt_inT (n : Nat) : inT (Jt n)=true :=
  Evidence.WF.inT_of_cnv _ (Jt_cnv n)

theorem Jt_lt_Z0t : ∀ n : Nat, lt (Jt n) Z0t=true
  | 0 => by decide
  | n+1 => by
    rw [Jt]
    unfold lt
    cases h:fuelOf (phi one (Jt n)) Z0t with
    | zero => simp [fuelOf] at h
    | succ f =>
      rw [Evidence.WF.ltF_succ_phi_Z]
      simp only [Bool.and_eq_true]
      have hf : one.deg+Z0t.deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      have hfj : (Jt n).deg+Z0t.deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      constructor
      · rw [← Evidence.WF.lt_eq_ltF one Z0t f hf]
        decide
      · rw [← Evidence.WF.lt_eq_ltF (Jt n) Z0t f hfj]
        exact Jt_lt_Z0t n

theorem Jt_lt_Z1 (n : Nat) : lt (Jt n) (Z one)=true :=
  Evidence.WF.lt_trans_inT (Jt_inT n) (by decide) (by decide)
    (Jt_lt_Z0t n) (by decide)

theorem Jt_lt_Jt_succ (n : Nat) : lt (Jt n) (Jt (n+1))=true := by
  rw [Jt]
  exact Evidence.WF.lt_phi_self (Jt_cnv n) one

theorem Bph_lt_Jt_succ : ∀ n : Nat, lt Bph (Jt (n+1))=true
  | 0 => Jt_lt_Jt_succ 0
  | n+1 => Evidence.WF.lt_trans_inT
      (by decide) (Jt_inT (n+1)) (Jt_inT (n+2))
      (Bph_lt_Jt_succ n) (Jt_lt_Jt_succ (n+1))

theorem Jt_succ_toList (n : Nat) : (Jt (n+1)).toList=[Jt (n+1)] := by
  rw [Jt]
  rfl

theorem Jt_succ_isAP (n : Nat) : (Jt (n+1)).isAP=true := by rw [Jt]; rfl

theorem Jt_succ_bne_one (n : Nat) : ((Jt (n+1))==one)=false := by rw [Jt]; rfl

theorem plus_Bph_Jt_succ (n : Nat) : plus Bph (Jt (n+1))=Jt (n+1) := by
  unfold plus
  rw [show Bph.toList=[Bph] from rfl,Jt_succ_toList]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (Jt (n+1)) Bph=false from by
    unfold le
    rw [show ((Jt (n+1)==Bph))=false from beq_eq_false_iff_ne.mpr
      (Ne.symm (Evidence.WF.ne_of_ltF (Bph_lt_Jt_succ n)))]
    simp only [Bool.false_or]
    exact Evidence.WF.lt_asymm_inT (by decide) (Jt_inT (n+1))
      (Bph_lt_Jt_succ n)]
  rfl

theorem omegaNF_Jt_succ (n : Nat) : omegaNF (Jt (n+1))=Jt (n+1) := by
  rw [Jt]
  exact (Rows.ProofsB.omegaNF_phi one (Jt n)).trans
    (Rows.ProofsB.phiNF_collapse (by decide))

theorem plus_Z0t_Jt_succ (n : Nat) :
    plus Z0t (Jt (n+1))=add Z0t (Jt (n+1)) := by
  unfold plus
  rw [show Z0t.toList=[Z0t] from rfl,Jt_succ_toList]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (Jt (n+1)) Z0t=true from Evidence.WF.le_of_lt (Jt_lt_Z0t (n+1))]
  rfl

theorem lt_M_add_Z0t_Jt_succ (n : Nat) :
    lt TM.Term.M (add Z0t (Jt (n+1)))=false := by
  unfold lt
  rw [show fuelOf TM.Term.M (add Z0t (Jt (n+1)))=
      (2*(TM.Term.M.deg+(add Z0t (Jt (n+1))).deg)+6)+1+1 from by
        unfold fuelOf
        omega,
    Evidence.WF.ltF_succ_M_add]
  simp only [show ((TM.Term.M:Term)==Z0t)=false from rfl,Bool.false_or,
    Evidence.WF.ltF_succ_M_Z]

theorem omegaNF_add_Z0t_Jt_succ (n : Nat) :
    omegaNF (add Z0t (Jt (n+1)))=phi zero (add Z0t (Jt (n+1))) := by
  rw [omegaNF_of_le_M (lt_M_add_Z0t_Jt_succ n)]
  exact Evidence.StageB.phiNF_add_pair rfl (Jt_succ_isAP n) (Jt_succ_bne_one n)

theorem collapse_one_Jt_succ (n : Nat) :
    Trans.Dict.collapse 1 (Jt (n+1))=
      phi zero (add Z0t (Jt (n+1))) := by
  have hw : Trans.Dict.wcnf (Z one) [Jt (n+1)]=([],Jt (n+1)) := by
    rw [Trans.Dict.wcnf,if_pos (Jt_lt_Z1 (n+1))]
    rfl
  unfold Trans.Dict.collapse
  rw [show Trans.Dict.reg (1+1)=Z one from rfl,
    show Trans.Dict.reg 1=Z0t from rfl,
    show ((1:Nat)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [Jt_succ_toList,hw]
  simp only [List.foldl_nil,Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left (Jt_succ_isAP n),plus_Z0t_Jt_succ,
    omegaNF_add_Z0t_Jt_succ]

def Kt (n : Nat) : Term := phi zero (add Z0t (Jt (n+1)))

theorem Jt_succ_lt_Htail (n : Nat) :
    lt (Jt (n+1)) (add Z0t (add Z0t one))=true :=
  Evidence.WF.lt_trans_inT (Jt_inT (n+1)) (by decide) (by decide)
    (Jt_lt_Z0t (n+1)) (by decide)

theorem add_Z0t_Jt_succ_lt_Hexp (n : Nat) :
    lt (add Z0t (Jt (n+1))) (add Z0t (add Z0t (add Z0t one)))=true := by
  rw [Evidence.WF.lt_add_add (by
    intro h
    injection h with _ hj
    exact Evidence.WF.ne_of_ltF (Jt_succ_lt_Htail n) hj),if_pos rfl]
  exact Jt_succ_lt_Htail n

theorem Kt_lt_H (n : Nat) : lt (Kt n) G9Dict.H=true := by
  change lt (phi zero (add Z0t (Jt (n+1))))
    (phi zero (add Z0t (add Z0t (add Z0t one))))=true
  rw [Evidence.WF.lt_pow]
  exact add_Z0t_Jt_succ_lt_Hexp n

theorem plus_H_Kt (n : Nat) : plus G9Dict.H (Kt n)=add G9Dict.H (Kt n) := by
  unfold plus
  rw [show G9Dict.H.toList=[G9Dict.H] from rfl,
    show (Kt n).toList=[Kt n] from by rw [Kt]; rfl]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (Kt n) G9Dict.H=true from Evidence.WF.le_of_lt (Kt_lt_H n)]
  rfl

theorem add_Z0t_Jt_succ_not_lt_Z0t (n : Nat) :
    lt (add Z0t (Jt (n+1))) Z0t=false := by
  unfold lt
  rw [show fuelOf (add Z0t (Jt (n+1))) Z0t=
      (2*((add Z0t (Jt (n+1))).deg+Z0t.deg)+7)+1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_add_nsum _ (by exact Term.noConfusion) (by rfl)]
  rw [← Evidence.WF.lt_eq_ltF Z0t Z0t _ (by simp only [Term.deg]; omega)]
  exact Evidence.WF.lt_irrefl Z0t

theorem Kt_not_lt_Z0t (n : Nat) : lt (Kt n) Z0t=false := by
  unfold Kt lt
  rw [show fuelOf (phi zero (add Z0t (Jt (n+1)))) Z0t=
      (2*((phi zero (add Z0t (Jt (n+1)))).deg+Z0t.deg)+7)+1 from by
        unfold fuelOf; omega,
    Evidence.WF.ltF_succ_phi_Z]
  rw [← Evidence.WF.lt_eq_ltF (add Z0t (Jt (n+1))) Z0t _ (by
    simp only [Term.deg]
    omega),add_Z0t_Jt_succ_not_lt_Z0t]
  simp only [Bool.and_false]

theorem phiShifted_add_Z0t_Jt_succ (n : Nat) :
    phiShifted zero (add Z0t (Jt (n+1)))=false := by
  unfold phiShifted
  rw [Evidence.StageB.splitFin_add_pair (Jt_succ_isAP n) (Jt_succ_bne_one n)]
  rfl

theorem logOm_Kt (n : Nat) : Trans.Dict.logOm (Kt n)=add Z0t (Jt (n+1)) := by
  unfold Kt Trans.Dict.logOm
  change (if phiShifted zero (add Z0t (Jt (n+1))) then
    plus (add Z0t (Jt (n+1))) one else add Z0t (Jt (n+1)))=_
  rw [phiShifted_add_Z0t_Jt_succ]
  rfl

theorem toList_add_Z0t_Jt_succ (n : Nat) :
    (add Z0t (Jt (n+1))).toList=[Z0t,Jt (n+1)] := by
  change Z0t::(Jt (n+1)).toList=_
  rw [Jt_succ_toList]

theorem wcnf_Kt (n : Nat) : Trans.Dict.wcnf Z0t [Kt n]=
    ([(one,Jt (n+1))],zero) := by
  unfold Trans.Dict.wcnf
  rw [Kt_not_lt_Z0t]
  simp only [Bool.false_eq_true,if_false,logOm_Kt]
  rw [toList_add_Z0t_Jt_succ]
  simp only [List.filter_cons,List.filter_nil,
    show lt Z0t Z0t=false from Evidence.WF.lt_irrefl Z0t,Jt_lt_Z0t,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false,
    List.map_cons,List.map_nil,
    show Trans.Dict.divAP Z0t Z0t=one from rfl,TM.Term.ofList,
    omegaNF_Jt_succ,Trans.Dict.wcnf]

theorem wcnf_H_Kt (n : Nat) : Trans.Dict.wcnf Z0t [G9Dict.H,Kt n]=
    ([(ofNat 3,omega),(one,Jt (n+1))],zero) := by
  rw [Trans.Dict.wcnf,if_neg (by decide)]
  simp only [G9Dict.H,Trans.Dict.logOm,TM.Term.phiShifted,TM.Term.splitFin,
    Bool.false_or,Bool.false_eq_true,if_false,TM.Term.toList,List.filter_cons,
    List.filter_nil,List.map_cons,List.map_nil,Trans.Dict.divAP,
    Trans.Dict.subAP]
  rw [wcnf_Kt]
  rfl

theorem phiNF_Jt_succ (n : Nat) : phiNF one (Jt (n+1))=Jt (n+2) := by
  rw [show Jt (n+1)=phi one (Jt n) from by rw [Jt],
    Rows.ProofsB.phiNF_phi_arg (a := one) (by rfl),Jt,Jt]

theorem collapse_H_Kt (n : Nat) :
    Trans.Dict.collapse 0 (plus G9Dict.H (Kt n))=Jt (n+2) := by
  have hap : (Jt (n+2)).isAP=true := by
    rw [show n+2=(n+1)+1 by omega,Jt_succ_isAP]
  have hom : omegaNF (Jt (n+2))=Jt (n+2) := by
    rw [show n+2=(n+1)+1 by omega,omegaNF_Jt_succ]
  rw [plus_H_Kt]
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show (add G9Dict.H (Kt n)).toList=[G9Dict.H,Kt n] from by
    rw [G9Dict.H,Kt]
    rfl,wcnf_H_Kt]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show le Z0t (TM.Term.ofNat 3)=false from by decide,
    show le Z0t one=false from by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Dict.sub1 omega=omega from rfl]
  simp only [Option.getD_some]
  rw [show (if (0==0) then zero else plus zero one)=zero from rfl,
    show phiNF (ofNat 3) (plus zero omega)=Bph from rfl,
    plus_Bph_Jt_succ,phiNF_Jt_succ,
    show plus (Jt (n+2)) zero=Jt (n+2) from rfl,
    Rows.ProofsB.plus_zero_left hap,hom]

theorem fs_raw (k : Nat) : fsN t k=iterPhiAt one (plus Bph one) k := by
  rw [t,fsN]
  rfl

theorem fs_Jt : ∀ n : Nat, fsN t (n+1)=Jt (n+1)
  | 0 => by rw [fs_raw]; rfl
  | n+1 => by
    have h : fsN t (n+2)=phiNF one (fsN t (n+1)) := by
      rw [fs_raw,fs_raw]
      rfl
    rw [h,fs_Jt n,Jt]
    exact Rows.ProofsB.phiNF_phi_arg (a := one) (by rfl)

theorem dict_D0_B0 : Trans.Dict.dict (.D 0 B0)=Jt 1 := by rfl

theorem dict_D0_W : ∀ n : Nat,
    Trans.Dict.dict (.D 0 (W n B0))=Jt (n+1)
  | 0 => dict_D0_B0
  | n+1 => by
    rw [W,Trans.Dict.dict_D,Trans.Dict.dict_sum,G9Dict.dict_A0,
      Trans.Dict.dict_D,dict_D0_W n,collapse_one_Jt_succ]
    exact collapse_H_Kt n

/-- Every complete six-column block advances the shifted family-four sequence. -/
theorem dict_LBT (n : Nat) :
    Trans.Dict.dict (LBT (6*n))=fsN t (n+1) := by
  rw [LBT_phase0]
  change Trans.Dict.dict (.D 0 (W n B0))=_
  rw [dict_D0_W,← fs_Jt]

theorem one_lt_Jt_succ (n : Nat) : lt one (Jt (n+1))=true :=
  Evidence.WF.lt_trans_inT (by decide) (by decide) (Jt_inT (n+1))
    (by decide) (Bph_lt_Jt_succ n)

theorem le_Jt_succ_one (n : Nat) : le (Jt (n+1)) one=false := by
  unfold le
  rw [show ((Jt (n+1))==one)=false from beq_eq_false_iff_ne.mpr
    (Ne.symm (Evidence.WF.ne_of_ltF (one_lt_Jt_succ n)))]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (by decide) (Jt_inT (n+1)) (one_lt_Jt_succ n)

theorem one_plus_Jt_succ (n : Nat) : plus one (Jt (n+1))=Jt (n+1) := by
  unfold plus
  rw [show one.toList=[one] from rfl,Jt_succ_toList]
  simp only [List.filter_cons,List.filter_nil,le_Jt_succ_one,Bool.false_eq_true,
    if_false,List.nil_append,TM.Term.ofList]

theorem one_plus_fs (n : Nat) : plus one (fsN t (n+1))=fsN t (n+1) := by
  rw [fs_Jt,one_plus_Jt_succ]

/-- The second disputed family-four row agrees with its shifted expansion sequence. -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fsN t (n+1)) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map
          Trans.Recal.transPort).map
            (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=some (fsN t (n+1))
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_L,dict_LBT,one_plus_fs]

#guard (List.range 18).all fun m =>
  Trans.Recal.redP (L m)==L m && Trans.Recal.transPort (L m)==LBT m
#guard (List.range 8).all fun n =>
  Trans.oR (BMS.expand M n)==some (fsN t (n+1))
#guard rest12.any fun r => r.m==M && r.t==t && r.proof=="namespace G10"
#guard (rows.filter fun r => r.proof=="namespace G10").length==1
#print axioms oR_M

end G10
end Rows.Selected
