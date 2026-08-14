import Rows.G8Dict

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G8

def M : BMS.Matrix := [[0,0],[1,1],[2,2],[3,1]]
def t : Term := psi (Z zero) (phi zero (add (Z (phi zero zero)) (Z zero)))

/-- Row-one value of an ascending tail column. -/
def q (a : Nat) : Int := (a % 3 : Nat)

/-- An ascending row-zero ladder with the periodic row-one pattern `0,1,2`. -/
def A (a p m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k => ((((a+k:Nat):Int)), q (p+k))

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS := (0,0) :: (1,1) :: (2,2) :: A 3 3 m

/-- Repeated reader wrapper contributed by a complete `0,1,2` block. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0, b => b
  | n+1, b => .D 0 (.D 2 (W n b))

/-- Reader output of the tail after `m` individual columns. -/
def Tail (m : Nat) : Trans.Dict.BT :=
  if m%3=0 then W (m/3) .zero
  else if m%3=1 then W (m/3) (.D 0 .zero)
  else W (m/3) (.D 0 (.D 1 .zero))

def LBT (m : Nat) : Trans.Dict.BT := .D 0 (.D 2 (Tail m))

theorem A_zero (a p : Nat) : A a p 0=[] := rfl

theorem A_succ (a p m : Nat) :
    A a p (m+1)=((((a:Nat):Int),q p))::A (a+1) (p+1) m := by
  unfold A
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · simp
    push_cast
    omega
  · simp
    congr 1
    omega

theorem A_succ_last (a p m : Nat) :
    A a p (m+1)=A a p m++[((((a+m:Nat):Int),q (p+m)))] := by
  unfold A
  rw [List.range_succ,List.map_append]
  simp [Nat.add_comm]

theorem length_A (a p m : Nat) : (A a p m).length=m := by simp [A]

theorem incrFirst_A (a p d m : Nat) :
    Trans.Recal.incrFirst (A a p m) (d:Int)=A (a+d) p m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · simp
    push_cast
    omega
  · simp

theorem incrFirst_A_neg (a p d m : Nat) (hd : d≤a) :
    Trans.Recal.incrFirst (A a p m) (-(d:Int))=A (a-d) p m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · simp
    push_cast
    omega
  · simp

theorem derp_A (a p m : Nat) :
    Trans.Recal.derp (A a p (m+1))=A (a+1) (p+1) m := by
  rw [A_succ]
  rfl

theorem L_succ (m : Nat) :
    L (m+1)=L m++[((((m+3:Nat):Int),q (m+3)))] := by
  unfold L
  rw [A_succ_last]
  simp [Nat.add_comm]

theorem length_L (m : Nat) : (L m).length=m+3 := by simp [L,length_A]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+3 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1))=L m := by
  rw [L_succ]
  unfold Trans.Recal.predP
  rw [show ((L m++[((((m+3:Nat):Int),q (m+3)))]).length==1)=false from by
    rw [List.length_append,length_L]
    simp]
  simp

/-! ### Link 1: expansion and parsing. -/

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,2]]++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,2]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 0++
      ((List.range (n+1)).map fun a =>
        ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
          [2+a*3*1,2+a*0*1]] : BMS.Matrix)).flatten) := rfl
  have hf : (fun a : Nat =>
      ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
        [2+a*3*1,2+a*0*1]] : BMS.Matrix))=
      fun a => [[3*a,0],[1+3*a,1],[2+3*a,2]] := by
    funext a
    simp [Nat.mul_comm]
  rw [h,hf,List.range_succ_eq_map]
  simp only [Option.getD_some,M,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.singleton_append,List.nil_append]
  have hb : ((fun a : Nat => ([[3*a,0],[1+3*a,1],[2+3*a,2]]:BMS.Matrix)) ∘ Nat.succ)=
      fun a => [[3+3*a,0],[4+3*a,1],[5+3*a,2]] := by
    funext a
    simp only [Function.comp_apply]
    rw [show 3*(a+1)=3+3*a by omega,
      show 1+(3+3*a)=4+3*a by omega,
      show 2+(3+3*a)=5+3*a by omega]
  rw [hb]

theorem q_three_mul (a : Nat) : q (3*a)=0 := by simp [q]
theorem q_three_mul_one (a : Nat) : q (3*a+1)=1 := by simp [q]
theorem q_three_mul_two (a : Nat) : q (3*a+2)=2 := by simp [q]

theorem A_three_mul (n : Nat) :
    A 3 3 (3*n)=((List.range n).map fun a =>
      ([(((3+3*a:Nat):Int),(0:Int)),(((4+3*a:Nat):Int),(1:Int)),
        (((5+3*a:Nat):Int),(2:Int))] : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega,A_succ_last,A_succ_last,A_succ_last,ih,
      List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc,
      List.singleton_append]
    rw [show 3+3*n=3*(n+1) by omega,
      show 3+(3*n+1)=3*n+4 by omega,
      show 3+(3*n+2)=3*n+5 by omega,
      q_three_mul (n+1),
      show 3*n+4=3*(n+1)+1 by omega,
      show 3*n+5=3*(n+1)+2 by omega,
      q_three_mul_one (n+1),q_three_mul_two (n+1)]
    rw [show 3*(n+1)+1=4+3*n by omega,
      show 3*(n+1)+2=5+3*n by omega]
    simp only [List.cons_append,List.nil_append]

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,2]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=A 3 3 (3*n) := by
  rw [A_three_mul]
  rw [List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,2]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by simp

/-- Link 1: each expansion lands on a three-column-complete prefix. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (3*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,2]]:BMS.Matrix)++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,2]]:BMS.Matrix)).flatten).isEmpty=false from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (3*n))
#guard (List.range 14).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard rest12.any fun r => r.m==M && r.t==t
#guard (rows.filter fun r => r.proof=="namespace G8").length==1

/-! ### Row-zero structure. -/

theorem getD_A (a p m k : Nat) (hk : k<m) :
    (A a p m).getD k (0,0)=((((a+k:Nat):Int),q (p+k))) := by
  unfold A
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem gp0_A (a p m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (A a p m) (k:Int)=((a+k:Nat):Int) := by
  show (if (k:Int)<0 then 0 else ((A a p m).getD k (0,0)).1)=_
  rw [if_neg (by omega),getD_A a p m k hk]

theorem gp1_A (a p m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (A a p m) (k:Int)=q (p+k) := by
  show (if (k:Int)<0 then 0 else ((A a p m).getD k (0,0)).2)=_
  rw [if_neg (by omega),getD_A a p m k hk]

theorem gp0_L (m k : Nat) (hk : k<m+3) :
    Trans.Recal.gp0 (L m) (k:Int)=(k:Int) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ j =>
        show (if ((j+3:Nat):Int)<0 then 0 else ((L m).getD (j+3) (0,0)).1)=_
        rw [if_neg (by omega)]
        change ((A 3 3 m).getD j (0,0)).1=_
        rw [getD_A 3 3 m j (by omega)]
        push_cast
        omega

theorem fpar_L (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar (L m) 0 (k:Int) 0=((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),gp0_L m k hk,length_L]
  obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show ((j+1:Nat):Int)-1=(j:Int) by omega,
    gp0_L m j (by omega),if_pos (by omega)]
  omega

theorem isAncAux_L (m k : Nat) : ∀ f : Nat, k<m+3 → k<f →
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f : Nat,k<m+3 → k<f →
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
      rw [fpar_L m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_L (m : Nat) : Trans.Recal.isPrincipalP (L m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (L m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_L]
    simp]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_L]; omega),length_L,lenI_L,
    show (m:Int)+3-1=((m+2:Nat):Int) by push_cast; omega]
  exact isAncAux_L m (m+2) (m+4) (by omega) (by omega)

/-! ### G8 reduction and reader. -/

-- The three-phase proof continues here.

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
    Trans.Recal.fpar0 (L (m+1)) 3 2=2 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  rw [Trans.Recal.fpar0Aux,if_neg (by omega)]
  rw [show (3:Int)-1=2 by omega,
    show Trans.Recal.gp0 (L (m+1)) 3=3 from gp0_L (m+1) 3 (by omega)]
  change (if Trans.Recal.gp0 (L (m+1)) 2<3 then 2 else _)=2
  rw [show Trans.Recal.gp0 (L (m+1)) 2=2 from rfl,if_pos (by omega)]

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

theorem gp1_L_three (m : Nat) : Trans.Recal.gp1 (L (m+1)) 3=0 := by
  show (if (3:Int)<0 then 0 else ((L (m+1)).getD 3 (0,0)).2)=0
  rw [if_neg (by omega)]
  change ((A 3 3 (m+1)).getD 0 (0,0)).2=0
  rw [getD_A 3 3 (m+1) 0 (by omega)]
  rfl

theorem fpar1_L_three_lb (m : Nat) :
    Trans.Recal.fpar (L (m+1)) 1 3 2=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_three,length_L]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_three_lb,if_neg (by omega)]
  rw [show Trans.Recal.fpar0 (L (m+1)) 2 2=-1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rw [if_pos (by omega)]]
  rw [show Trans.Recal.gp1 (L (m+1)) 2=2 from rfl,
    if_neg (by omega),if_pos (by omega)]

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

/-- A nonempty strictly ascending tail. -/
def N (a p m : Nat) : Trans.Recal.PS :=
  (((a:Nat):Int),q p)::A (a+1) (p+1) m

theorem A_eq_N (a p m : Nat) : A a p (m+1)=N a p m := by
  rw [A_succ]
  rfl

theorem length_N (a p m : Nat) : (N a p m).length=m+1 := by
  simp [N,length_A]

theorem lenI_N (a p m : Nat) : Trans.Recal.lenI (N a p m)=(m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_N]
  omega

theorem gp0_N (a p m k : Nat) (hk : k<m+1) :
    Trans.Recal.gp0 (N a p m) (k:Int)=((a+k:Nat):Int) := by
  cases k with
  | zero => rfl
  | succ k =>
    show (if ((k+1:Nat):Int)<0 then 0 else ((N a p m).getD (k+1) (0,0)).1)=_
    rw [if_neg (by omega)]
    change ((A (a+1) (p+1) m).getD k (0,0)).1=_
    rw [getD_A (a+1) (p+1) m k (by omega)]
    push_cast
    omega

theorem fpar_N (a p m k : Nat) (hk0 : 0<k) (hk : k<m+1) :
    Trans.Recal.fpar (N a p m) 0 (k:Int) 0=((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_N]; omega),if_pos (by rfl),
    gp0_N a p m k hk,length_N]
  obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show ((j+1:Nat):Int)-1=(j:Int) by omega,
    gp0_N a p m j (by omega),if_pos (by omega)]
  push_cast
  omega

theorem fpar_N_zero (a p m : Nat) :
    Trans.Recal.fpar (N a p m) 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_N]; omega),if_pos (by rfl),length_N]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem isAncAux_N (a p m k : Nat) : ∀ f : Nat, k<m+1 → k<f →
    Trans.Recal.isAncAux f (N a p m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f : Nat,k<m+1 → k<f →
    Trans.Recal.isAncAux f (N a p m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
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
      rw [fpar_N a p m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_N (a p m : Nat) (hm : 0<m) :
    Trans.Recal.isPrincipalP (N a p m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (N a p m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_N]
    rw [show (m+1==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
    rfl]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_N]; omega),length_N,lenI_N,
    show (m:Int)+1-1=(m:Int) by omega]
  exact isAncAux_N a p m m (m+2) (by omega) (by omega)

theorem fAncAux_N_last (a p m k : Nat) : ∀ (f : Nat) (acc : List Int),
    k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (N a p m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ (f : Nat) (acc : List Int),
    k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (N a p m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      rw [show Trans.Recal.fpar (N a p m) 0 ((0:Nat):Int) 0=-1 from by
        simpa using fpar_N_zero a p m,if_neg (by omega)]
      exact hlast
    · rw [fpar_N a p m k (by omega) hkm,if_pos (by omega)]
      exact ih (k-1) (by omega) f (acc++[((k-1:Nat):Int)])
        (by omega) (by omega) (by simp)

theorem fAnc_N_last (a p m : Nat) :
    (Trans.Recal.fAnc (N a p m) 0 (m:Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_N]; omega),length_N]
  exact fAncAux_N_last a p m m (m+2) [(m:Int)]
    (by omega) (by omega) (by simp)

theorem slice_N_full (a p m : Nat) :
    Trans.Recal.slice (N a p m) 0 ((m+1:Nat):Int)=N a p m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show (((m+1:Nat):Int)-0).toNat=m+1 by omega]
  simpa only [length_N] using
    (List.take_length : (N a p m).take (N a p m).length=N a p m)

theorem ppair_N (a p m : Nat) : Trans.Recal.ppair (N a p m)=[N a p m] := by
  unfold Trans.Recal.ppair
  rw [length_N,lenI_N]
  simp only [Trans.Recal.ppairAux]
  rw [if_neg (by omega),show (m:Int)+1-1=(m:Int) by omega,fAnc_N_last]
  simp only [Option.getD_some]
  rw [show (m:Int)+1=((m+1:Nat):Int) by omega,slice_N_full]
  rw [if_pos (by omega)]

theorem brF_L_zero : Trans.Recal.brF (L 0)=[] := by rfl

theorem brF_L_succ (m : Nat) :
    Trans.Recal.brF (L (m+1))=[A 3 3 (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_L]
  change Trans.Recal.ppair (A 3 3 (m+1))=[A 3 3 (m+1)]
  rw [A_eq_N,ppair_N]

theorem firstNodes_L_succ (m : Nat) :
    Trans.Recal.firstNodes (L (m+1))=[3,((m+4:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L_succ,trMax_L]
  simp [length_A]
  omega

theorem joints_L_succ (m : Nat) : Trans.Recal.joints (L (m+1))=[2] := by
  unfold Trans.Recal.joints
  rw [firstNodes_L_succ]
  change [Trans.Recal.fpar (L (m+1)) 0 3 0]=[2]
  congr 1
  simpa using fpar_L (m+1) 3 (by omega) (by omega)

theorem q_add_three (a : Nat) : q (a+3)=q a := by
  unfold q
  omega

theorem A_phase_add_three (a p m : Nat) : A a (p+3) m=A a p m := by
  unfold A
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · rfl
  · simp only
    rw [show p+3+k=(p+k)+3 by omega,q_add_three]

theorem A_zero_add_three (m : Nat) : A 0 3 (m+3)=L m := by
  rw [show m+3=((m+2)+1) by omega,A_succ]
  rw [show m+2=((m+1)+1) by omega,A_succ]
  rw [A_succ]
  simp only [q]
  change (0,0)::(1,1)::(2,2)::A 3 6 m=L m
  rw [A_phase_add_three]
  rfl

theorem red_A_three_one (f : Nat) :
    Trans.Recal.red (f+1) (A 3 3 1)=A 0 3 1 := by
  rfl

theorem red_A_zero_two (f : Nat) :
    Trans.Recal.red (f+1) (A 0 3 2)=A 0 3 2 := by
  change Trans.Recal.red (f+1) (G1.LG 0)=G1.LG 0
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (G1.LG 0)=false from by rfl,
    G1.isPrincipalP_LG]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (G1.LG 0) 0==0 &&
      Trans.Recal.gp1 (G1.LG 0) 0==0)=true from by rfl]
  simp only [if_true]
  rw [G1.trMax_LG,G1.lenI_LG]
  rfl

theorem red_A_three_step (m f : Nat)
    (hred : Trans.Recal.red f (A 0 3 (m+2))=A 0 3 (m+2)) :
    Trans.Recal.red (f+1) (A 3 3 (m+2))=A 0 3 (m+2) := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (A 3 3 (m+2))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_A]
    simp]
  rw [show Trans.Recal.isPrincipalP (A 3 3 (m+2))=true from by
    rw [A_eq_N]
    exact isPrincipalP_N 3 3 (m+1) (by omega)]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (A 3 3 (m+2)) 0==0 &&
      Trans.Recal.gp1 (A 3 3 (m+2)) 0==0)=false from by
    rw [show Trans.Recal.gp0 (A 3 3 (m+2)) 0=3 from by
        simpa using gp0_A 3 3 (m+2) 0 (by omega),
      show Trans.Recal.gp1 (A 3 3 (m+2)) 0=0 from by
        simpa using gp1_A 3 3 (m+2) 0 (by omega)]
    rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (A 3 3 (m+2)) 0==0)=true from by
    rw [show Trans.Recal.gp1 (A 3 3 (m+2)) 0=0 from by
      simpa using gp1_A 3 3 (m+2) 0 (by omega)]
    rfl]
  simp only [if_true]
  rw [show Trans.Recal.incrFirst (A 3 3 (m+2))
      (-Trans.Recal.gp0 (A 3 3 (m+2)) 0)=A 0 3 (m+2) from by
    rw [show Trans.Recal.gp0 (A 3 3 (m+2)) 0=3 from by
      simpa using gp0_A 3 3 (m+2) 0 (by omega)]
    simpa using incrFirst_A_neg 3 3 3 (m+2) (by omega)]
  exact hred

theorem red_L_bound : ∀ m f : Nat, 4*m+5≤f →
    Trans.Recal.red f (L m)=L m := by
  intro m
  refine Nat.strongRecOn (motive:=fun m => ∀ f : Nat, 4*m+5≤f →
    Trans.Recal.red f (L m)=L m) m ?_
  intro m ih f hf
  obtain ⟨g,rfl⟩ : ∃ g,f=g+1 := ⟨f-1,by omega⟩
  cases m with
  | zero =>
    rw [Trans.Recal.red]
    rfl
  | succ m =>
    rw [Trans.Recal.red]
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
    rw [show ([A 3 3 (m+1)] : List Trans.Recal.PS).getD 0 []=
        A 3 3 (m+1) from rfl,
      show ([3,((m+4:Nat):Int)] : List Int).getD 0 0=3 from rfl,
      show ([2] : List Int).getD 0 0=2 from rfl]
    rw [show Trans.Recal.gp1 (A 3 3 (m+1)) 0=0 from by
      simpa using gp1_A 3 3 (m+1) 0 (by omega)]
    simp only [show ((0:Int)==0)=true from rfl,if_true]
    rw [show ((2+1,-1+1)::Trans.Recal.derp (A 3 3 (m+1)))=
        A 3 3 (m+1) from by
      rw [A_succ]
      rfl,
      show (2:Int)-(-1)=3 by omega]
    change Trans.Recal.jjSeq 0 2 ++ Trans.Recal.incrFirst
      (Trans.Recal.red g (A 3 3 (m+1))) 3=L (m+1)
    have htail : Trans.Recal.red g (A 3 3 (m+1))=A 0 3 (m+1) := by
      cases m with
      | zero =>
        obtain ⟨h,rfl⟩ : ∃ h,g=h+1 := ⟨g-1,by omega⟩
        exact red_A_three_one h
      | succ p =>
        obtain ⟨h,rfl⟩ : ∃ h,g=h+1 := ⟨g-1,by omega⟩
        apply red_A_three_step p h
        cases p with
        | zero =>
          obtain ⟨u,rfl⟩ : ∃ u,h=u+1 := ⟨h-1,by omega⟩
          exact red_A_zero_two u
        | succ r =>
          rw [show r+1+2=r+3 by omega,A_zero_add_three]
          apply ih r (by omega) h
          omega
    rw [htail]
    rw [show Trans.Recal.incrFirst (A 0 3 (m+1)) 3=A 3 3 (m+1) from by
      simpa using incrFirst_A 0 3 3 (m+1)]
    rfl

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
/-! ### Three-phase reader steps. -/

theorem gp1_L_tail (m k : Nat) (hk0 : 3≤k) (hk : k<m+3) :
    Trans.Recal.gp1 (L m) (k:Int)=q k := by
  obtain ⟨j,rfl⟩ : ∃ j,k=j+3 := ⟨k-3,by omega⟩
  show (if ((j+3:Nat):Int)<0 then 0 else ((L m).getD (j+3) (0,0)).2)=_
  rw [if_neg (by omega)]
  change ((A 3 3 m).getD j (0,0)).2=q (j+3)
  rw [getD_A 3 3 m j (by omega)]
  rw [show 3+j=j+3 by omega]

theorem fpar0_L_adj (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar0 (L m) (k:Int) ((k-1:Nat):Int)=((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m k hk]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show ((k:Nat):Int)-1=((k-1:Nat):Int) by omega,
    gp0_L m (k-1) (by omega),if_pos (by omega)]

theorem fpar0_L_self (m k : Nat) (hk : k<m+3) :
    Trans.Recal.fpar0 (L m) (k:Int) (k:Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m k hk]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_adj (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar (L m) 1 (k:Int) ((k-1:Nat):Int)=
      if Trans.Recal.gp1 (L m) ((k-1:Nat):Int)<Trans.Recal.gp1 (L m) (k:Int)
      then ((k-1:Nat):Int) else -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_adj m k hk0 hk,if_neg (by omega)]
  by_cases hlt : Trans.Recal.gp1 (L m) ((k-1:Nat):Int)<
      Trans.Recal.gp1 (L m) (k:Int)
  · simp only [if_pos hlt]
  · simp only [if_neg hlt]
    rw [fpar0_L_self m (k-1) (by omega),if_pos (by omega)]

theorem isParent1_L_adj_false (m k : Nat) (hk0 : 0<k) (hk : k<m+3)
    (hlt : ¬ Trans.Recal.gp1 (L m) ((k-1:Nat):Int)<
      Trans.Recal.gp1 (L m) (k:Int)) :
    Trans.Recal.isParentP (L m) 1 (k:Int) ((k-1:Nat):Int)=false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_L_adj m k hk0 hk,lenI_L]
  rw [show decide (0≤((k-1:Nat):Int))=true from decide_eq_true (by omega),
    show decide (((k-1:Nat):Int)<(m:Int)+3)=true from decide_eq_true (by omega)]
  simp only [Bool.true_and]
  rw [if_neg hlt,show (((k-1:Nat):Int)==(-1:Int))=false from
    beq_eq_false_iff_ne.mpr (by omega)]

theorem isParent1_L_adj_true (m k : Nat) (hk0 : 0<k) (hk : k<m+3)
    (hlt : Trans.Recal.gp1 (L m) ((k-1:Nat):Int)<
      Trans.Recal.gp1 (L m) (k:Int)) :
    Trans.Recal.isParentP (L m) 1 (k:Int) ((k-1:Nat):Int)=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_L_adj m k hk0 hk,lenI_L]
  rw [show decide (0≤((k-1:Nat):Int))=true from decide_eq_true (by omega),
    show decide (((k-1:Nat):Int)<(m:Int)+3)=true from decide_eq_true (by omega)]
  simp only [Bool.true_and]
  rw [if_pos hlt]
  exact G1.beq_Int_self _

theorem gp1_L_phase0 (a : Nat) :
    Trans.Recal.gp1 (L (3*a+1)) ((3*a+3:Nat):Int)=0 := by
  rw [gp1_L_tail (3*a+1) (3*a+3) (by omega) (by omega)]
  simp [q]

theorem gp1_L_phase1 (a : Nat) :
    Trans.Recal.gp1 (L (3*a+2)) ((3*a+3:Nat):Int)=0 := by
  rw [gp1_L_tail (3*a+2) (3*a+3) (by omega) (by omega)]
  simp [q]

theorem gp1_L_phase1_top (a : Nat) :
    Trans.Recal.gp1 (L (3*a+2)) ((3*a+4:Nat):Int)=1 := by
  rw [gp1_L_tail (3*a+2) (3*a+4) (by omega) (by omega)]
  simp [q]

theorem gp1_L_phase2_zero (a : Nat) :
    Trans.Recal.gp1 (L (3*a+3)) ((3*a+3:Nat):Int)=0 := by
  rw [gp1_L_tail (3*a+3) (3*a+3) (by omega) (by omega)]
  simp [q]

theorem gp1_L_phase2_one (a : Nat) :
    Trans.Recal.gp1 (L (3*a+3)) ((3*a+4:Nat):Int)=1 := by
  rw [gp1_L_tail (3*a+3) (3*a+4) (by omega) (by omega)]
  simp [q]

theorem gp1_L_phase2_two (a : Nat) :
    Trans.Recal.gp1 (L (3*a+3)) ((3*a+5:Nat):Int)=2 := by
  rw [gp1_L_tail (3*a+3) (3*a+5) (by omega) (by omega)]
  simp [q]

theorem isAdm_L_phase0 (a : Nat) :
    Trans.Recal.isAdm (L (3*a+1)) ((3*a+2:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((3*a+2:Nat):Int)>Trans.Recal.lenI (L (3*a+1)))=false
    from decide_eq_false (by rw [lenI_L]; push_cast; omega)]
  simp only [Bool.false_or]
  rw [show ((3*a+2:Nat):Int)+1=((3*a+3:Nat):Int) by omega]
  have hp : Trans.Recal.isParentP (L (3*a+1)) 1 ((3*a+3:Nat):Int)
      ((3*a+2:Nat):Int)=false := by
    apply isParent1_L_adj_false (3*a+1) (3*a+3) (by omega) (by omega)
    rw [show 3*a+3-1=3*a+2 by omega]
    cases a with
    | zero => decide
    | succ a =>
      rw [gp1_L_tail (3*(a+1)+1) (3*(a+1)+2) (by omega) (by omega),
        gp1_L_tail (3*(a+1)+1) (3*(a+1)+3) (by omega) (by omega)]
      simp [q]
  rw [hp,Bool.and_false]
  rfl

theorem isAdm_L_phase1_at (a extra : Nat) :
    Trans.Recal.isAdm (L (3*a+2+extra)) ((3*a+3:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((3*a+3:Nat):Int)>Trans.Recal.lenI (L (3*a+2+extra)))=false
    from decide_eq_false (by rw [lenI_L]; push_cast; omega)]
  simp only [Bool.false_or]
  rw [show ((3*a+3:Nat):Int)-1=((3*a+2:Nat):Int) by omega]
  have hp : Trans.Recal.isParentP (L (3*a+2+extra)) 1 ((3*a+3:Nat):Int)
      ((3*a+2:Nat):Int)=false := by
    apply isParent1_L_adj_false (3*a+2+extra) (3*a+3) (by omega) (by omega)
    rw [show 3*a+3-1=3*a+2 by omega]
    cases a with
    | zero =>
      change ¬ Trans.Recal.gp1 (L (2+extra)) 2<
        Trans.Recal.gp1 (L (2+extra)) 3
      have htop : Trans.Recal.gp1 (L (2+extra)) 3=0 := by
        simpa [q] using gp1_L_tail (2+extra) 3 (by omega) (by omega)
      rw [show Trans.Recal.gp1 (L (2+extra)) 2=2 from rfl,htop]
      omega
    | succ a =>
      rw [gp1_L_tail (3*(a+1)+2+extra) (3*(a+1)+2) (by omega) (by omega),
        gp1_L_tail (3*(a+1)+2+extra) (3*(a+1)+3) (by omega) (by omega)]
      simp [q]
  rw [hp,Bool.false_and]
  rfl

theorem isAdm_L_phase2_false (a : Nat) :
    Trans.Recal.isAdm (L (3*a+3)) ((3*a+4:Nat):Int)=false := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((3*a+4:Nat):Int)>Trans.Recal.lenI (L (3*a+3)))=false
    from decide_eq_false (by rw [lenI_L]; push_cast; omega)]
  simp only [Bool.false_or]
  rw [show ((3*a+4:Nat):Int)-1=((3*a+3:Nat):Int) by omega,
    show ((3*a+4:Nat):Int)+1=((3*a+5:Nat):Int) by omega]
  have hp0 : Trans.Recal.isParentP (L (3*a+3)) 1 ((3*a+4:Nat):Int)
      ((3*a+3:Nat):Int)=true := by
    apply isParent1_L_adj_true (3*a+3) (3*a+4) (by omega) (by omega)
    rw [show 3*a+4-1=3*a+3 by omega]
    rw [gp1_L_phase2_zero,gp1_L_phase2_one]
    omega
  have hp1 : Trans.Recal.isParentP (L (3*a+3)) 1 ((3*a+5:Nat):Int)
      ((3*a+4:Nat):Int)=true := by
    apply isParent1_L_adj_true (3*a+3) (3*a+5) (by omega) (by omega)
    rw [show 3*a+5-1=3*a+4 by omega]
    rw [gp1_L_phase2_one,gp1_L_phase2_two]
    omega
  rw [hp0,hp1]
  rfl

theorem adm_L_phase0 (a : Nat) :
    Trans.Recal.adm (L (3*a+1)) ((3*a+2:Nat):Int)=((3*a+2:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase0,if_pos rfl]

theorem adm_L_phase1 (a : Nat) :
    Trans.Recal.adm (L (3*a+2)) ((3*a+3:Nat):Int)=((3*a+3:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a 0,if_pos rfl]

theorem adm_L_phase2 (a : Nat) :
    Trans.Recal.adm (L (3*a+3)) ((3*a+4:Nat):Int)=((3*a+3:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase2_false,if_neg (by decide)]
  simp only [show ((3*a+4:Nat):Int)-1=((3*a+3:Nat):Int) by omega,
    Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a 1,if_pos rfl]

theorem gp1_L_phase0_parent (a : Nat) :
    Trans.Recal.gp1 (L (3*a+1)) ((3*a+2:Nat):Int)=2 := by
  cases a with
  | zero => rfl
  | succ a =>
    rw [gp1_L_tail (3*(a+1)+1) (3*(a+1)+2) (by omega) (by omega)]
    simp [q]

theorem transType_L_phase0 (a : Nat) :
    Trans.Recal.transTypeMain (L (3*a+1)) ((3*a+2:Nat):Int)
      ((3*a+3:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase0]
  simp only [show ((0:Int)==0)=true from rfl,if_true]
  rw [isAdm_L_phase0,if_pos rfl]

theorem transType_L_phase1 (a : Nat) :
    Trans.Recal.transTypeMain (L (3*a+2)) ((3*a+3:Nat):Int)
      ((3*a+4:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase1_top]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase1]
  rw [if_neg (by omega)]
  rw [if_neg (by push_cast; omega)]

theorem transType_L_phase2 (a : Nat) :
    Trans.Recal.transTypeMain (L (3*a+3)) ((3*a+4:Nat):Int)
      ((3*a+5:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase2_two]
  simp only [show ((2:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase2_one]
  rw [if_neg (by omega)]
  rw [if_neg (by push_cast; omega)]

abbrev D2z : Trans.Dict.BT := .D 2 .zero
abbrev D0z : Trans.Dict.BT := .D 0 .zero
abbrev D01z : Trans.Dict.BT := .D 0 (.D 1 .zero)
abbrev D02z : Trans.Dict.BT := .D 0 (.D 2 .zero)

theorem mkC2_L_phase0 (a : Nat) :
    Trans.Recal.mkC2 (L (3*a+1)) ((3*a+2:Nat):Int)
      ((3*a+3:Nat):Int) 1 D2z=.D 2 D0z := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase0]
  rfl

theorem mkC2_L_phase1 (a : Nat) :
    Trans.Recal.mkC2 (L (3*a+2)) ((3*a+3:Nat):Int)
      ((3*a+4:Nat):Int) 6 D0z=D01z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L_phase1_top]
  rfl

theorem mkC2_L_phase2 (a : Nat) :
    Trans.Recal.mkC2 (L (3*a+3)) ((3*a+4:Nat):Int)
      ((3*a+5:Nat):Int) 6 D01z=D02z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L_phase2_two]
  rfl

theorem Tail_phase0 (a : Nat) : Tail (3*a)=W a .zero := by
  unfold Tail
  rw [if_pos (by omega)]
  congr 1
  omega

theorem Tail_phase1 (a : Nat) : Tail (3*a+1)=W a D0z := by
  unfold Tail
  rw [if_neg (by omega),if_pos (by omega)]
  congr 1
  omega

theorem Tail_phase2 (a : Nat) : Tail (3*a+2)=W a D01z := by
  unfold Tail
  rw [if_neg (by omega),if_neg (by omega)]
  congr 1
  omega

theorem LBT_phase0 (a : Nat) : LBT (3*a)=W (a+1) .zero := by
  rw [LBT,Tail_phase0]
  rfl

theorem LBT_phase1 (a : Nat) : LBT (3*a+1)=W (a+1) D0z := by
  rw [LBT,Tail_phase1]
  rfl

theorem LBT_phase2 (a : Nat) : LBT (3*a+2)=W (a+1) D01z := by
  rw [LBT,Tail_phase2]
  rfl

theorem size_W (n : Nat) (b : Trans.Dict.BT) :
    (W n b).size=2*n+b.size := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    simp only [W,Trans.Dict.BT.size,ih]
    omega

theorem repl_W_D2 : ∀ (n f : Nat), 2*n+3≤f →
    Trans.Recal.replMark f (W (n+1) .zero) D2z (.D 2 D0z)=
      some (W (n+1) D0z)
  | 0, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+3 := ⟨f-3,by omega⟩
    change Trans.Recal.replMark (g+3) (.D 0 D2z) D2z (.D 2 D0z)=
      some (.D 0 (.D 2 D0z))
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 D2z)==D2z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [G1.replMark_self (g+2) 2 .zero (.D 2 D0z) (by omega)]
    rfl
  | n+1, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+2 := ⟨f-2,by omega⟩
    change Trans.Recal.replMark (g+2) (.D 0 (.D 2 (W (n+1) .zero)))
      D2z (.D 2 D0z)=some (.D 0 (.D 2 (W (n+1) D0z)))
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.D 2 (W (n+1) .zero)))==D2z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+1=g+1 by rfl,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 2 (W (n+1) .zero))==D2z)=false from by
      cases n <;> rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [repl_W_D2 n g (by omega)]
    rfl

theorem repl_W_D0 : ∀ (n f : Nat), 2*n+2≤f →
    Trans.Recal.replMark f (W n D0z) D0z D01z=some (W n D01z)
  | 0, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+1 := ⟨f-1,by omega⟩
    change Trans.Recal.replMark (g+1) D0z D0z D01z=some D01z
    exact G1.replMark_self (g+1) 0 .zero D01z (by omega)
  | n+1, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+2 := ⟨f-2,by omega⟩
    change Trans.Recal.replMark (g+2) (.D 0 (.D 2 (W n D0z))) D0z D01z=
      some (.D 0 (.D 2 (W n D01z)))
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.D 2 (W n D0z)))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+1=g+1 by rfl,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 2 (W n D0z))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [repl_W_D0 n g (by omega)]
    rfl

theorem repl_W_D01 : ∀ (n f : Nat), 2*n+2≤f →
    Trans.Recal.replMark f (W n D01z) D01z D02z=some (W n D02z)
  | 0, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+1 := ⟨f-1,by omega⟩
    change Trans.Recal.replMark (g+1) D01z D01z D02z=some D02z
    exact G1.replMark_self (g+1) 0 (.D 1 .zero) D02z (by omega)
  | n+1, f, hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+2 := ⟨f-2,by omega⟩
    change Trans.Recal.replMark (g+2) (.D 0 (.D 2 (W n D01z))) D01z D02z=
      some (.D 0 (.D 2 (W n D02z)))
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.D 2 (W n D01z)))==D01z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+1=g+1 by rfl,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 2 (W n D01z))==D01z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [repl_W_D01 n g (by omega)]
    rfl

theorem repl_LBT_phase0 (a f : Nat) (hf : 2*a+5≤f) :
    Trans.Recal.replMark f (LBT (3*a)) D2z (.D 2 D0z)=
      some (LBT (3*a+1)) := by
  rw [LBT_phase0,LBT_phase1]
  exact repl_W_D2 a f (by omega)

theorem repl_LBT_phase1 (a f : Nat) (hf : 2*a+4≤f) :
    Trans.Recal.replMark f (LBT (3*a+1)) D0z D01z=
      some (LBT (3*a+2)) := by
  rw [LBT_phase1,LBT_phase2]
  exact repl_W_D0 (a+1) f (by omega)

theorem W_D02 (n : Nat) : W n D02z=W (n+1) .zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [W]
    rw [ih]
    rfl

theorem repl_LBT_phase2 (a f : Nat) (hf : 2*a+4≤f) :
    Trans.Recal.replMark f (LBT (3*a+2)) D01z D02z=
      some (LBT (3*(a+1))) := by
  rw [LBT_phase2,LBT_phase0]
  rw [show a+1+1=(a+1)+1 by rfl,← W_D02 (a+1)]
  exact repl_W_D01 (a+1) f (by omega)

/-! ### Memo invariant. -/

def Allowed (k : Nat) (req : Option Int) : Prop :=
  if k%3=2 then req=none ∨ req=some ((k+1:Nat):Int)
  else req=none ∨ req=some ((k+2:Nat):Int)

def Val (k : Nat) (req : Option Int) : Trans.Dict.BT :=
  if req=none then LBT k
  else if k%3=0 then D2z else if k%3=1 then D0z else D01z

theorem Allowed_none (k : Nat) : Allowed k none := by
  unfold Allowed
  split <;> exact Or.inl rfl

theorem Val_none (k : Nat) : Val k none=LBT k := by
  rw [Val,if_pos rfl]

theorem Allowed_phase0 (a : Nat) :
    Allowed (3*a) (some ((3*a+2:Nat):Int)) := by
  rw [Allowed,if_neg (by omega)]
  exact Or.inr rfl

theorem Allowed_phase1 (a : Nat) :
    Allowed (3*a+1) (some ((3*a+3:Nat):Int)) := by
  rw [Allowed,if_neg (by omega)]
  exact Or.inr (by congr 2 <;> omega)

theorem Allowed_phase2 (a : Nat) :
    Allowed (3*a+2) (some ((3*a+3:Nat):Int)) := by
  rw [Allowed,if_pos (by omega)]
  exact Or.inr (by congr 2 <;> omega)

theorem Val_phase0 (a : Nat) :
    Val (3*a) (some ((3*a+2:Nat):Int))=D2z := by
  rw [Val,if_neg (by intro h; cases h),if_pos (by omega)]

theorem Val_phase1 (a : Nat) :
    Val (3*a+1) (some ((3*a+3:Nat):Int))=D0z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_pos (by omega)]

theorem Val_phase2 (a : Nat) :
    Val (3*a+2) (some ((3*a+3:Nat):Int))=D01z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega)]

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
    have hd:=congrArg (fun z => z.getD 3 ((0:Int),(0:Int))) h
    simp [L,A,G2.L2,List.replicate_succ,q] at hd

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
      rw [Allowed,if_neg (by decide)] at hr
      rcases hr with h|h <;> cases h
    · intro h
      exact absurd (congrArg Prod.fst h) (L_ne_base k)
  · intro j r h _
    have hL:L k=L j:=congrArg Prod.fst h
    have hkj:=L_inj k j hL
    subst hkj
    have hreq:req=r:=by simpa using congrArg Prod.snd h
    subst hreq
    rfl

theorem good_L2_entry (k : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 0) :
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
  · intro j r h ha
    obtain ⟨hj,hk⟩:=L_eq_L2 j k (congrArg Prod.fst h).symm
    subst hj
    subst hk
    have hreq:req=r:=by simpa using congrArg Prod.snd h
    subst hreq
    rcases hr with h|h
    · subst h
      rfl
    · subst h
      rw [Allowed,if_neg (by decide)] at ha
      rcases ha with h|h <;> cases h

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
    (req : Option Int) (hr : req=none ∨ req=some 0) :
    Sound (((G2.L2 k,req),G2.L2BT k)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    exact good_L2_entry k req hr
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
    (h : tbl.find? (fun z=>z.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h),?_⟩
  have hb:p.1==key:=List.find?_some (p:=fun z=>z.1==key) (a:=p) h
  exact eq_of_beq hb

theorem value_L_of_good {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (hg : Good p) (k : Nat) (req : Option Int) (hr : Allowed k req)
    (he : p.1=(L k,req)) : p.2=Val k req :=
  hg.2 k req he hr

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

theorem runAux_L20 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 0) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) (G2.L2 0) req).run tbl).1=G2.L2BT 0 ∧
      Sound ((Trans.Recal.runAux (g+2) (G2.L2 0) req).run tbl).2 := by
  cases hf:tbl.find? (fun z=>z.1==(G2.L2 0,req)) with
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
      rw [show (Trans.Recal.runAux (g+1) G1.Base none).run tbl=(a,s) from hrun]
        at ih
      have ha:a=Trans.Dict.BT.zero:=ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,
        if_true]
      rcases hr with h|h
      · subst h
        exact ⟨rfl,Sound_cons_L2 s hsm 0 none (Or.inl rfl)⟩
      · subst h
        exact ⟨rfl,Sound_cons_L2 s hsm 0 (some 0) (Or.inr rfl)⟩

theorem adm_L_zero_one : Trans.Recal.adm (L 0) 1=0 := by rfl
theorem transType_L_zero : Trans.Recal.transTypeMain (L 0) 1 2=6 := by rfl
theorem mkC2_L_zero :
    Trans.Recal.mkC2 (L 0) 1 2 6 (G2.L2BT 0)=LBT 0 := by rfl

set_option maxHeartbeats 1000000 in
theorem runAux_L0 (g : Nat) (req : Option Int) (hr : Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).2 := by
  have hr' : req=none ∨ req=some 2 := by
    rw [Allowed,if_neg (by decide)] at hr
    simpa using hr
  cases hf:tbl.find? (fun z=>z.1==(L 0,req)) with
  | some p =>
    rw [show g+3=(g+2)+1 by omega,G1.run_hit (g+2) (L 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg 0 req hr he,hs⟩
  | none =>
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L 0,isPrincipalP_L 0,
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L 0,
      show (((0:Int)+3-1)==0)=false from by decide,
      show Trans.Recal.predP (L 0)=G2.L2 0 from rfl]
    cases hrun:(Trans.Recal.runAux (g+2) (G2.L2 0) none) tbl with
    | mk a s =>
      have ih1:=runAux_L20 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) none).run tbl=(a,s)
        from hrun] at ih1
      have ha:a=G2.L2BT 0:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      cases hrun2:(Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)) s with
      | mk c1 s2 =>
        have ih2:=runAux_L20 g (some 0) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=G2.L2BT 0:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((0:Nat):Int)+3-1)=2 by omega,
          show ((2:Int)==0)=false from rfl,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((G2.L2BT 0)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (L 0) 0 2 0=1 from by rfl,adm_L_zero_one,
          hrun2,transType_L_zero,mkC2_L_zero]
        rcases hr' with h|h
        · subst h
          have hrepl : Trans.Recal.replMark
              ((G2.L2BT 0).size+((G2.L2BT 0).size+(LBT 0).size+4))
              (G2.L2BT 0) (G2.L2BT 0) (LBT 0)=some (LBT 0) := by
            change Trans.Recal.replMark
              ((G2.L2BT 0).size+((G2.L2BT 0).size+(LBT 0).size+4))
              (.D 0 (.D 1 .zero)) (.D 0 (.D 1 .zero)) (LBT 0)=some (LBT 0)
            exact G1.replMark_self _ 0 (.D 1 .zero) (LBT 0) (by omega)
          rw [hrepl]
          refine ⟨Val_none 0,?_⟩
          have ht:=Sound_cons_L s2 hsm2 0 none (Allowed_none 0)
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬((2:Int)<(3:Int)-1) by omega,if_false,
            show Trans.Recal.gp1 (L 0) ((0:Int)+3-1)=2 from by rfl,
            StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          have hv : Val 0 (some 2)=D2z := by simpa using Val_phase0 0
          refine ⟨hv.symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 0 (some 2) (Allowed_phase0 0)
          rw [hv] at ht
          exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase0_step (a g : Nat) (req : Option Int)
    (hr : Allowed (3*a+1) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (3*a) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux (3*a+g+3) (L (3*a)) r).run s).1=Val (3*a) r ∧
          Sound ((Trans.Recal.runAux (3*a+g+3) (L (3*a)) r).run s).2) :
    ((Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1)) req).run tbl).1=
        Val (3*a+1) req ∧
      Sound ((Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((3*a+3:Nat):Int) := by
    rw [Allowed,if_neg (by omega)] at hr
    simpa only [show 3*a+1+2=3*a+3 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (3*a+1),req)) with
  | some p =>
    rw [show (3*a+1)+g+3=(3*a+g+3)+1 by omega,
      G1.run_hit (3*a+g+3) (L (3*a+1)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (3*a+1) req hr he,hs⟩
  | none =>
    rw [show (3*a+1)+g+3=(3*a+g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (3*a+1),isPrincipalP_L (3*a+1),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (3*a+1),
      show ((((3*a+1:Nat):Int)+3-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (3*a+1))=L (3*a) from by
        simpa only [show 3*a+1=3*a+1 by rfl] using predP_L (3*a)]
    cases hrun:(Trans.Recal.runAux (3*a+g+3) (L (3*a)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (3*a)) tbl hs
      rw [show (Trans.Recal.runAux (3*a+g+3) (L (3*a)) none).run tbl=(t1,s)
        from hrun] at ih1
      have ht1:t1=LBT (3*a):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      simp only [show (((3*a+1:Nat):Int)+3-1)=((3*a+3:Nat):Int) by omega,
        StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hrun,
        show ((LBT (3*a))==Trans.Dict.BT.zero)=false from by
          rw [LBT_phase0]; rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (L (3*a+1)) 0 ((3*a+3:Nat):Int) 0=
          ((3*a+2:Nat):Int) from by
            simpa using fpar_L (3*a+1) (3*a+3) (by omega) (by omega),
        adm_L_phase0]
      cases hrun2:(Trans.Recal.runAux (3*a+g+3) (L (3*a))
          (some ((3*a+2:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((3*a+2:Nat):Int)) (Allowed_phase0 a) s hsm
        rw [show (Trans.Recal.runAux (3*a+g+3) (L (3*a))
          (some ((3*a+2:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D2z:=ih2.1.trans (Val_phase0 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun2,transType_L_phase0,mkC2_L_phase0]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase0 a _ (by
            rw [LBT_phase0,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (3*a+1),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (3*a+1) none (Allowed_none (3*a+1))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬(((3*a+3:Nat):Int)<((3*a+3:Nat):Int)) by omega,
            if_false,gp1_L_phase0,StateT.run,bind,StateT.bind,StateT.get,
            StateT.pure,pure,modify,modifyGet,MonadStateOf.modifyGet,
            StateT.modifyGet,get,getThe,MonadStateOf.get,Id.run]
          refine ⟨(Val_phase1 a).symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 (3*a+1)
            (some ((3*a+3:Nat):Int)) (Allowed_phase1 a)
          rw [Val_phase1] at ht
          exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase1_step (a g : Nat) (req : Option Int)
    (hr : Allowed (3*a+2) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (3*a+1) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1)) r).run s).1=
            Val (3*a+1) r ∧
          Sound ((Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1)) r).run s).2) :
    ((Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2)) req).run tbl).1=
        Val (3*a+2) req ∧
      Sound ((Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((3*a+3:Nat):Int) := by
    rw [Allowed,if_pos (by omega)] at hr
    simpa only [show 3*a+2+1=3*a+3 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (3*a+2),req)) with
  | some p =>
    rw [show (3*a+2)+g+3=((3*a+1)+g+3)+1 by omega,
      G1.run_hit ((3*a+1)+g+3) (L (3*a+2)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (3*a+2) req hr he,hs⟩
  | none =>
    rw [show (3*a+2)+g+3=((3*a+1)+g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (3*a+2),isPrincipalP_L (3*a+2),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (3*a+2),
      show ((((3*a+2:Nat):Int)+3-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (3*a+2))=L (3*a+1) from by
        simpa only [show 3*a+2=(3*a+1)+1 by omega] using predP_L (3*a+1)]
    cases hrun:(Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (3*a+1)) tbl hs
      rw [show (Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (3*a+1):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      simp only [show (((3*a+2:Nat):Int)+3-1)=((3*a+4:Nat):Int) by omega,
        StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hrun,
        show ((LBT (3*a+1))==Trans.Dict.BT.zero)=false from by
          rw [LBT_phase1]; rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (L (3*a+2)) 0 ((3*a+4:Nat):Int) 0=
          ((3*a+3:Nat):Int) from by
            simpa using fpar_L (3*a+2) (3*a+4) (by omega) (by omega),
        adm_L_phase1]
      cases hrun2:(Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1))
          (some ((3*a+3:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((3*a+3:Nat):Int)) (Allowed_phase1 a) s hsm
        rw [show (Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1))
          (some ((3*a+3:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D0z:=ih2.1.trans (Val_phase1 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun2,transType_L_phase1,mkC2_L_phase1]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase1 a _ (by
            rw [LBT_phase1,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (3*a+2),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (3*a+2) none (Allowed_none (3*a+2))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show (((3*a+3:Nat):Int)<((3*a+4:Nat):Int)) by omega,
            if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          cases hrun3:(Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1))
              (some ((3*a+3:Nat):Int))) s2 with
          | mk c0 s3 =>
            have ih3:=ih (some ((3*a+3:Nat):Int)) (Allowed_phase1 a) s2 hsm2
            rw [show (Trans.Recal.runAux ((3*a+1)+g+3) (L (3*a+1))
              (some ((3*a+3:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
            have hc0:c0=D0z:=ih3.1.trans (Val_phase1 a)
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (G1.isMarkedB_self D0z),
              G1.replMark_self (D0z.size+(D0z.size+D01z.size+4))
                0 .zero D01z (by omega)]
            refine ⟨(Val_phase2 a).symm,?_⟩
            have ht:=Sound_cons_L s3 hsm3 (3*a+2)
              (some ((3*a+3:Nat):Int)) (Allowed_phase2 a)
            rw [Val_phase2] at ht
            exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase2_step (a g : Nat) (req : Option Int)
    (hr : Allowed (3*a+3) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (3*a+2) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2)) r).run s).1=
            Val (3*a+2) r ∧
          Sound ((Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2)) r).run s).2) :
    ((Trans.Recal.runAux ((3*a+3)+g+3) (L (3*a+3)) req).run tbl).1=
        Val (3*a+3) req ∧
      Sound ((Trans.Recal.runAux ((3*a+3)+g+3) (L (3*a+3)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((3*a+5:Nat):Int) := by
    rw [Allowed,if_neg (by omega)] at hr
    simpa only [show 3*a+3+2=3*a+5 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (3*a+3),req)) with
  | some p =>
    rw [show (3*a+3)+g+3=((3*a+2)+g+3)+1 by omega,
      G1.run_hit ((3*a+2)+g+3) (L (3*a+3)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (3*a+3) req hr he,hs⟩
  | none =>
    rw [show (3*a+3)+g+3=((3*a+2)+g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (3*a+3),isPrincipalP_L (3*a+3),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (3*a+3),
      show ((((3*a+3:Nat):Int)+3-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (3*a+3))=L (3*a+2) from by
        simpa only [show 3*a+3=(3*a+2)+1 by omega] using predP_L (3*a+2)]
    cases hrun:(Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (3*a+2)) tbl hs
      rw [show (Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (3*a+2):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      simp only [show (((3*a+3:Nat):Int)+3-1)=((3*a+5:Nat):Int) by omega,
        StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hrun,
        show ((LBT (3*a+2))==Trans.Dict.BT.zero)=false from by
          rw [LBT_phase2]; rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (L (3*a+3)) 0 ((3*a+5:Nat):Int) 0=
          ((3*a+4:Nat):Int) from by
            simpa using fpar_L (3*a+3) (3*a+5) (by omega) (by omega),
        adm_L_phase2]
      cases hrun2:(Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2))
          (some ((3*a+3:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((3*a+3:Nat):Int)) (Allowed_phase2 a) s hsm
        rw [show (Trans.Recal.runAux ((3*a+2)+g+3) (L (3*a+2))
          (some ((3*a+3:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D01z:=ih2.1.trans (Val_phase2 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun2,transType_L_phase2,mkC2_L_phase2]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase2 a _ (by
            rw [LBT_phase2,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (3*a+3),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (3*a+3) none (Allowed_none (3*a+3))
          rw [Val_none] at ht
          exact ht

        · subst h
          simp only [show ¬(((3*a+5:Nat):Int)<((3*a+5:Nat):Int)) by omega,
            if_false,gp1_L_phase2_two,StateT.run,bind,StateT.bind,StateT.get,
            StateT.pure,pure,modify,modifyGet,MonadStateOf.modifyGet,
            StateT.modifyGet,get,getThe,MonadStateOf.get,Id.run]
          refine ⟨(Val_phase0 (a+1)).symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 (3*a+3)
            (some ((3*a+5:Nat):Int)) (by
              simpa only [show 3*(a+1)=3*a+3 by omega,
                show 3*(a+1)+2=3*a+5 by omega] using Allowed_phase0 (a+1))
          rw [show Val (3*a+3) (some ((3*a+5:Nat):Int))=D2z from by
            simpa only [show 3*(a+1)=3*a+3 by omega,
              show 3*(a+1)+2=3*a+5 by omega] using Val_phase0 (a+1)] at ht
          exact ht
def RunOK (k : Nat) : Prop :=
  ∀ g : Nat, ∀ req : Option Int, Allowed k req →
    ∀ tbl : Trans.Recal.Memo, Sound tbl →
      ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).1=Val k req ∧
        Sound ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).2

theorem runOK_zero : RunOK 0 := by
  intro g req hr tbl hs
  simpa only [Nat.zero_add] using runAux_L0 g req hr tbl hs

theorem runOK_phase0 (a : Nat) (ih : RunOK (3*a)) : RunOK (3*a+1) := by
  intro g req hr tbl hs
  exact runAux_phase0_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase1 (a : Nat) (ih : RunOK (3*a+1)) : RunOK (3*a+2) := by
  intro g req hr tbl hs
  exact runAux_phase1_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase2 (a : Nat) (ih : RunOK (3*a+2)) : RunOK (3*a+3) := by
  intro g req hr tbl hs
  exact runAux_phase2_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_triple (a : Nat) :
    RunOK (3*a) ∧ RunOK (3*a+1) ∧ RunOK (3*a+2) := by
  induction a with
  | zero =>
    have h0 : RunOK (3*0) := by simpa only using runOK_zero
    have h1:=runOK_phase0 0 h0
    exact ⟨h0,h1,runOK_phase1 0 h1⟩
  | succ a ih =>
    have h0' := runOK_phase2 a ih.2.2
    have h0 : RunOK (3*(a+1)) := by
      simpa only [show 3*(a+1)=3*a+3 by omega] using h0'
    have h1:=runOK_phase0 (a+1) h0
    exact ⟨h0,h1,runOK_phase1 (a+1) h1⟩

set_option maxHeartbeats 2000000 in
theorem runAux_L (k g : Nat) (req : Option Int) (hr : Allowed k req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).2 := by
  have hk : RunOK k := by
    have hm : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
    have hdiv:=Nat.mod_add_div k 3
    rcases hm with h0|h1|h2
    · have heq:k=3*(k/3):=by omega
      rw [heq]
      exact (runOK_triple (k/3)).1
    · have heq:k=3*(k/3)+1:=by omega
      rw [heq]
      exact (runOK_triple (k/3)).2.1
    · have heq:k=3*(k/3)+2:=by omega
      rw [heq]
      exact (runOK_triple (k/3)).2.2
  exact hk g req hr tbl hs

/-- Link 2: the recalibrated reader follows the entire three-phase ladder. -/
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

theorem W_eq_dict (n : Nat) (b : Trans.Dict.BT) :
    W n b=G8Dict.W n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [W,G8Dict.W,ih]

/-- Link 3: every complete `0,1,2` block advances the selected fundamental sequence. -/
theorem dict_LBT (n : Nat) :
    Trans.Dict.dict (LBT (3*n))=fsN t n := by
  rw [LBT_phase0,W_eq_dict]
  simpa only [t,G8Dict.t,G8Dict.Z0,G8Dict.Z1,TM.Term.one] using
    G8Dict.dict_W_fsN n

theorem fsN_eq_F (n : Nat) : fsN t n=G8Dict.F n := by
  simpa only [t,G8Dict.t,G8Dict.Z0,G8Dict.Z1,TM.Term.one] using
    G8Dict.fsN_t n

theorem one_plus_fsN (n : Nat) : plus TM.Term.one (fsN t n)=fsN t n := by
  rw [fsN_eq_F]
  cases n <;> rw [G8Dict.F] <;>
    unfold plus <;>
    rw [show TM.Term.one.toList=[TM.Term.one] from rfl,
      show (psi (Z zero) _).toList=[psi (Z zero) _] from rfl] <;>
    simp only [List.filter_cons,List.filter_nil,G2.le_psi_one,
      Bool.false_eq_true,if_false,List.nil_append,TM.Term.ofList]

/-- The selected first-`Omega_1`-inside-`psi_2` row agrees with its expansion sequence. -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fsN t n) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map
          Trans.Recal.transPort).map
            (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=some (fsN t n)
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_L,dict_LBT,one_plus_fsN]

#guard (List.range 16).all fun m =>
  Trans.Recal.redP (L m)==L m && Trans.Recal.transPort (L m)==LBT m
#guard (List.range 8).all fun n =>
  Trans.oR (BMS.expand M n)==some (fsN t n)
#print axioms oR_M
end G8
end Rows.Selected
