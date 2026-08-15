import Rows.G10
import Rows.Ladder

/-!
# G12 — Γ_{ψ₀(Ω₂)+1} の行 `(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`

`oR` が要る 12 行の最後の 1 行。展開の値の列は標準基本列ではなく閉じた形 `fD`
(`Rows/Selected.lean`) で、`Certified` の極限節はそれで構わない。

**リンク 1 と 3 が定理になっている。残るのはリンク 2 だけである。**

    展開 --ofMatrix--> 梯子 --transPort--> BT --dict--> 値
            ✅ ofMatrix_M      🚧 未着手      ✅ dict_LBT

この行の読み出し出力は高さ 3 の族の中では**最も単純**で、`W` は 1 つの構成子の
繰り返しになる (`G10` は 6 相、`G11` は 7 相)。周期は 5 列、行 0 の値はブロックごとに
3 ずつ増える。

リンク 3 の形:

    dict (D 0 (W n Base))          = fD n
    dict D2z = Z 1
    collapse 1 (fD n)              = Ct n = φ̄(0, Ω + fD n)
    collapse 1 (Ct n)              = Dt n = φ̄(0, Ct n)        -- Ω は増えない
    collapse 0 (Z 1 + Dt n)        = fD (n+1)

**2 段目で `Ω` が増えない**のは、1 段目の値が既に `Ω` より大きく `plus` の filter が
`Ω` を落とすためである。`G10`/`G11` はここで `Ω` が増える。

最後の段は `collapse` の**強臨界の枝**を通る唯一の場所で、そこで `ψ_Ω(Z1) = Cps` が
出て、続く Veblen の枝がそれを底に使う。だから `fD (n+1) = φ̄(fD n, Cps+1)` になる。

**この行の値は Veblen 断片ではない** (`CNV (fD 0) = false`)。`ψ`/`Z` を含むので、
`Evidence/WF.lean` の `CNV` 用の道具は使えず、順序の事実は `inT` の上で取り直してある。
-/

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G12

def M : BMS.Matrix := [[0,0],[1,1],[2,2],[1,1],[2,1],[3,1]]
def t : Term := psi (Z zero) (add (Z (phi zero zero)) (phi zero zero))

/-- Row-zero value of the `0,1,2,1,1` five-column tail; the block steps by 3. -/
def p (k : Nat) : Int :=
  if k%5=0 then ((3*(k/5)+3:Nat):Int)
  else if k%5=1 ∨ k%5=3 then ((3*(k/5)+4:Nat):Int)
  else ((3*(k/5)+5:Nat):Int)

/-- Row-one value of the five-column tail. -/
def q (k : Nat) : Int := if k%5=0 then 0 else if k%5=2 then 2 else 1

def T (m : Nat) : Trans.Recal.PS := (List.range m).map fun k => (p k,q k)

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS := [(0,0),(1,1),(2,2),(1,1),(2,1)]++T m

abbrev D0z : Trans.Dict.BT := .D 0 .zero
abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev D2z : Trans.Dict.BT := .D 2 .zero
abbrev D11z : Trans.Dict.BT := .D 1 D1z
abbrev Base : Trans.Dict.BT := .sum D2z D11z

/-- A complete block wraps the unfinished suffix in the reader output. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0,b => b
  | n+1,b => .sum D2z (.D 1 (.D 1 (.D 0 (W n b))))

def Part : Nat → Trans.Dict.BT
  | 0 => Base
  | 1 => .sum D2z (.D 1 (.D 1 D0z))
  | 2 => .sum D2z (.D 1 (.D 1 (.D 0 D1z)))
  | 3 => .sum D2z (.D 1 (.D 1 (.D 0 D2z)))
  | _ => .sum D2z (.D 1 (.D 1 (.D 0 (.sum D2z D1z))))

/-- Reader output on every one-column prefix of the five-phase ladder. -/
def LBT (m : Nat) : Trans.Dict.BT := .D 0 (W (m/5) (Part (m%5)))

theorem T_succ (m : Nat) : T (m+1)=T m++[(p m,q m)] := by
  unfold T
  rw [List.range_succ,List.map_append]
  rfl

theorem L_succ (m : Nat) : L (m+1)=L m++[(p m,q m)] := by
  unfold L
  rw [T_succ,List.append_assoc]

theorem length_T (m : Nat) : (T m).length=m := by simp [T]

theorem length_L (m : Nat) : (L m).length=m+5 := by simp [L,length_T]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+5 := by
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
      ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
        [2+a*3*1,2+a*0*1],[1+a*3*1,1+a*0*1],
        [2+a*3*1,1+a*0*1]] : BMS.Matrix))=
      fun a => [[3*a,0],[1+3*a,1],[2+3*a,2],[1+3*a,1],[2+3*a,1]] := by
  funext a
  simp [Nat.mul_comm]

theorem expand_block_succ : ((fun a : Nat =>
      ([[3*a,0],[1+3*a,1],[2+3*a,2],[1+3*a,1],[2+3*a,1]]:BMS.Matrix)) ∘ Nat.succ)=
      fun a => [[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] := by
  funext a
  simp only [Function.comp_apply]
  rw [show 3*(a+1)=3+3*a by omega,
    show 1+(3+3*a)=4+3*a by omega,
    show 2+(3+3*a)=5+3*a by omega]

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,2],[1,1],[2,1]]++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 0++
      ((List.range (n+1)).map fun a =>
        ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
          [2+a*3*1,2+a*0*1],[1+a*3*1,1+a*0*1],
          [2+a*3*1,1+a*0*1]] : BMS.Matrix)).flatten) := rfl
  rw [h,expand_block_first,List.range_succ_eq_map]
  simp only [Option.getD_some,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.nil_append]
  rw [expand_block_succ]

theorem p_phase0 (a : Nat) : p (5*a)=((3*a+3:Nat):Int) := by simp [p]
theorem p_phase1 (a : Nat) : p (5*a+1)=((3*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase2 (a : Nat) : p (5*a+2)=((3*a+5:Nat):Int) := by simp [p]; omega
theorem p_phase3 (a : Nat) : p (5*a+3)=((3*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase4 (a : Nat) : p (5*a+4)=((3*a+5:Nat):Int) := by simp [p]; omega
theorem q_phase0 (a : Nat) : q (5*a)=0 := by simp [q]
theorem q_phase1 (a : Nat) : q (5*a+1)=1 := by simp [q]
theorem q_phase2 (a : Nat) : q (5*a+2)=2 := by simp [q]
theorem q_phase3 (a : Nat) : q (5*a+3)=1 := by simp [q]
theorem q_phase4 (a : Nat) : q (5*a+4)=1 := by simp [q]

theorem T_five_mul (n : Nat) :
    T (5*n)=((List.range n).map fun a =>
      ([(((3*a+3:Nat):Int),(0:Int)),(((3*a+4:Nat):Int),(1:Int)),
        (((3*a+5:Nat):Int),(2:Int)),(((3*a+4:Nat):Int),(1:Int)),
        (((3*a+5:Nat):Int),(1:Int))]
        : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5*n+5 by omega,T_succ,T_succ,T_succ,T_succ,T_succ,ih,
      List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc,
      List.singleton_append]
    rw [p_phase0 n,q_phase0 n,p_phase1 n,q_phase1 n,p_phase2 n,q_phase2 n,
      p_phase3 n,q_phase3 n,p_phase4 n,q_phase4 n]
    simp only [List.cons_append,List.nil_append]

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=T (5*n) := by
  rw [T_five_mul,List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  change [(((3+3*a:Nat):Int),0),(((4+3*a:Nat):Int),1),
    (((5+3*a:Nat):Int),2),(((4+3*a:Nat):Int),1),
    (((5+3*a:Nat):Int),1)]=_
  rw [show 3+3*a=3*a+3 by omega,show 4+3*a=3*a+4 by omega,
    show 5+3*a=3*a+5 by omega]

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by simp

/-- Link 1: each expansion lands on a five-column-complete prefix. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (5*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,2],[1,1],[2,1]]:BMS.Matrix)++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]]:BMS.Matrix)).flatten).isEmpty=false
      from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

/-! ### Link 2 — what the reduction does, measured

`redP (L m) = L m` is the first branch `runAux` tests, so link 2 cannot start without it.
The recursion `red` takes on this ladder is, at each level, ONE branch (`brF` has length 1)
and the fold rebuilds the prefix:

    red (L m)   = jjSeq 0 2 ++ incrFirst (red (V m)) 0        V m = (L m).drop 3
    red (V m)   = incrFirst ((red (Q m)).drop 1) 0            Q m = (0,0) :: incrFirst (V m) 1
    red (Q m)   = jjSeq 0 1 ++ incrFirst (red ((2,1) :: TS 1 m)) 1

with `trMax (L m) = 2` and `joints (L m) = [0]` CONSTANT in `m`, which is what makes the
ladder uniform.  Below is the arithmetic the induction runs on; the induction itself is not
done.  Everything here is a theorem, and the shapes above are pinned by `#guard`. -/

/-! ### Link 2, step 1: the tail is 5-periodic up to a shift of 3. -/

theorem p_add_five (k : Nat) : p (k+5)=p k+3 := by
  unfold p
  rw [show (k+5)%5=k%5 by omega,show (k+5)/5=k/5+1 by omega]
  by_cases h0 : k%5=0
  · rw [if_pos h0,if_pos h0]
    push_cast
    omega
  · rw [if_neg h0,if_neg h0]
    by_cases h1 : k%5=1 ∨ k%5=3
    · rw [if_pos h1,if_pos h1]
      push_cast
      omega
    · rw [if_neg h1,if_neg h1]
      push_cast
      omega

theorem q_add_five (k : Nat) : q (k+5)=q k := by
  unfold q
  rw [show (k+5)%5=k%5 by omega]

/-- The tail with every row-zero entry shifted by `d`. -/
def TS (d : Int) (m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k => (p k+d,q k)

theorem TS_zero (m : Nat) : TS 0 m=T m := by
  unfold TS T
  apply List.map_congr_left
  intro k _
  simp

theorem TS_succ (d : Int) (m : Nat) : TS d (m+1)=TS d m++[(p m+d,q m)] := by
  unfold TS
  rw [List.range_succ,List.map_append]
  rfl

theorem length_TS (d : Int) (m : Nat) : (TS d m).length=m := by simp [TS]

theorem incrFirst_TS (d e : Int) (m : Nat) :
    Trans.Recal.incrFirst (TS d m) e=TS (d+e) m := by
  unfold Trans.Recal.incrFirst TS
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  show ((p k+d)+e,q k)=(p k+(d+e),q k)
  rw [Int.add_assoc]

/-- The five-column period, as a statement about the shifted tail. -/
theorem TS_add_five (d : Int) : ∀ m : Nat, TS d (m+5)=TS d 5++TS (d+3) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show m+1+5=(m+5)+1 by omega,TS_succ,ih,List.append_assoc]
    congr 1
    rw [TS_succ (d+3) m,p_add_five m,q_add_five m,
      show p m+3+d=p m+(d+3) from by omega]

/-- `S m` is the tail read as a ladder in its own right: `S (m+5) = L m`. -/
def S (m : Nat) : Trans.Recal.PS := TS (-3) m

theorem TS_neg3_five : TS (-3) 5=[(0,0),(1,1),(2,2),(1,1),(2,1)] := by decide

theorem S_add_five (m : Nat) : S (m+5)=L m := by
  show TS (-3) (m+5)=_
  rw [TS_add_five]
  show TS (-3) 5++TS ((-3)+3) m=L m
  rw [show (-3:Int)+3=0 by omega,TS_zero]
  unfold L
  rw [TS_neg3_five]

#guard (List.range 8).all fun m => S (m+5)==L m
#guard (List.range 8).all fun m => TS 0 m==T m
-- 上の測定を留めておく
#guard (List.range 10).all fun m => Trans.Recal.trMax (L m)==2
#guard (List.range 10).all fun m => Trans.Recal.joints (L m)==[0]
#guard (List.range 10).all fun m => (Trans.Recal.brF (L m)).length==1
#guard (List.range 10).all fun m => Trans.Recal.ppair (L m)==[L m]


/-! ### Link 2, step 2: the recursion is a FIVE-PHASE family, and `red` forgets the shift

MEASURED, and it is what makes the induction finite.  Writing `D h d m` for
`(h,1) :: Tf i d m`:

    redP (D h d m)              is INDEPENDENT of `h` and of `d`
    redP ((0,0) :: D h d m)     likewise, and equals `(0,0) ::` the former
    trMax ((0,0) :: D h d m) = 1,  brF has length 1,  joints = [1]

`red` normalises the shift away, so the whole recursion is indexed by the OFFSET `i` into
the tail and by the remaining length `m` alone.  Each level drops one column and advances
the offset by one; offsetting by five is a shift of three, so the offset lives mod 5.

    red (L m) = jjSeq 0 2 ++ incrFirst (red (V m)) 0
    red (V m) = incrFirst ((red (Q m)).drop 1) 0
    red (Q m) = jjSeq 0 1 ++ incrFirst (red ((2,1) :: Tf 1 1 m)) 1
    red ((h,1) :: Tf i d (m+1))  descends to  (h',1) :: Tf (i+1) d' m

The three facts the descent runs on are theorems below; the induction over them is not
written.  This is the same shape as `Rows/G10.lean`'s six-phase cycle, one phase shorter. -/

/-- The tail read from offset `i`, with every row-zero entry shifted by `d`.
    `red`'s recursion advances `i` by one and drops one column at each level. -/
def Tf (i : Nat) (d : Int) (m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k => (p (k+i)+d,q (k+i))

theorem Tf_zero (d : Int) (m : Nat) : Tf 0 d m=TS d m := by
  unfold Tf TS
  apply List.map_congr_left
  intro k _
  rfl

/-- The five-phase period: offsetting by five is a shift of three. -/
theorem Tf_add_five (i : Nat) (d : Int) (m : Nat) : Tf (i+5) d m=Tf i (d+3) m := by
  unfold Tf
  apply List.map_congr_left
  intro k _
  show (p (k+(i+5))+d,q (k+(i+5)))=(p (k+i)+(d+3),q (k+i))
  rw [show k+(i+5)=(k+i)+5 by omega,p_add_five,q_add_five]
  congr 1
  omega

/-- One level of `red`'s recursion: drop a column, advance the offset. -/
theorem Tf_drop (i : Nat) (d : Int) (m : Nat) :
    (Tf i d (m+1)).drop 1=Tf (i+1) d m := by
  unfold Tf
  rw [List.range_succ_eq_map,List.map_cons,List.drop_succ_cons,List.drop_zero,
    List.map_map]
  apply List.map_congr_left
  intro k _
  show (p (k+1+i)+d,q (k+1+i))=(p (k+(i+1))+d,q (k+(i+1)))
  rw [show k+1+i=k+(i+1) by omega]

#guard (List.range 6).all fun m => (List.range 4).all fun dd =>
  Tf 0 (dd:Int) m == TS (dd:Int) m
#guard (List.range 6).all fun m => (List.range 3).all fun i => (List.range 4).all fun dd =>
  Tf (i+5) (dd:Int) m == Tf i ((dd:Int)+3) m
#guard (List.range 6).all fun m => (List.range 5).all fun i => (List.range 4).all fun dd =>
  (Tf i (dd:Int) (m+1)).drop 1 == Tf (i+1) (dd:Int) m
-- 正規形は先頭の値にも shift にも依らない (測定)
#guard (List.range 5).all fun i => (List.range 4).all fun m =>
  Trans.Recal.redP (((2:Int),(1:Int)) :: Tf i 1 m)
    == Trans.Recal.redP (((5:Int),(1:Int)) :: Tf i 3 m)

#guard (List.range 6).all fun m => (List.range 4).all fun dd =>
  Tf 0 (dd:Int) m == TS (dd:Int) m
#guard (List.range 6).all fun m => (List.range 3).all fun i => (List.range 4).all fun dd =>
  Tf (i+5) (dd:Int) m == Tf i ((dd:Int)+3) m
#guard (List.range 6).all fun m => (List.range 5).all fun i => (List.range 4).all fun dd =>
  (Tf i (dd:Int) (m+1)).drop 1 == Tf (i+1) (dd:Int) m
-- 正規形は先頭の値にも shift にも依らない (測定)
#guard (List.range 5).all fun i => (List.range 4).all fun m =>
  Trans.Recal.redP (((2:Int),(1:Int)) :: Tf i 1 m)
    == Trans.Recal.redP (((5:Int),(1:Int)) :: Tf i 3 m)
#guard (List.range 6).all fun m =>
  Trans.Recal.trMax (((0:Int),(0:Int)) :: ((2:Int),(1:Int)) :: Tf 1 1 m)==1

/-! ### Link 2, step 3: the row-zero and row-one parents of the base columns. -/

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

theorem fpar0_L_three (m : Nat) : Trans.Recal.fpar0 (L m) 3 2=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  show (if (3:Int)-1<2 then -1
        else if Trans.Recal.gp0 (L m) ((3:Int)-1)<Trans.Recal.gp0 (L m) 3 then (3:Int)-1
        else Trans.Recal.fpar0Aux (m+5) (L m) (Trans.Recal.gp0 (L m) 3)
          ((3:Int)-1-1) 2)=-1
  rw [if_neg (by omega),
    show Trans.Recal.gp0 (L m) ((3:Int)-1)=2 from rfl,
    show Trans.Recal.gp0 (L m) 3=1 from rfl,
    if_neg (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_one (m : Nat) : Trans.Recal.fpar (L m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 1 0
    if j1<0 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+5) (L m) 1 j1 0)=0
  rw [fpar0_L_one]
  rfl

theorem fpar1_L_two (m : Nat) : Trans.Recal.fpar (L m) 1 2 1=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 2 1
    if j1<1 then -1 else if Trans.Recal.gp1 (L m) j1<2 then j1
    else Trans.Recal.fpar1Aux (m+5) (L m) 2 j1 1)=1
  rw [fpar0_L_two]
  rfl

theorem fpar1_L_three_lb (m : Nat) : Trans.Recal.fpar (L m) 1 3 2=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 3 2
    if j1<2 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+5) (L m) 1 j1 2)=-1
  rw [fpar0_L_three]
  rw [if_pos (by omega)]

/-- `trMax` は `m` に依らず 2。梯子が一様であることの中身。 -/
theorem trMax_L (m : Nat) : Trans.Recal.trMax (L m)=2 := by
  show Trans.Recal.trMaxAux ((L m).length+1) (L m) 0=2
  rw [length_L]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1) 0=true from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1) 0=0 from by simpa using fpar1_L_one m]
    unfold Trans.Recal.lenI
    rw [length_L]
    rw [show decide ((0:Int)<((m+5:Nat):Int))=true from decide_eq_true (by omega)]
    rfl]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1+1) (0+1)=true from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1+1) (0+1)=1 from by simpa using fpar1_L_two m]
    unfold Trans.Recal.lenI
    rw [length_L]
    rw [show decide ((0:Int)≤0+1)=true from decide_eq_true (by omega),
      show decide ((0:Int)+1<((m+5:Nat):Int))=true from decide_eq_true (by omega)]
    rfl]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1+1+1) (0+1+1)=false from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1+1+1) (0+1+1)=-1 from by
      simpa using fpar1_L_three_lb m]
    simp]
  simp

/-! ### Link 2, step 4: the ladder's row-zero and row-one values in closed form.

The base and the tail turn out to obey the SAME formula, which is what makes the
parent structure uniform. -/

/-- Row-zero value at index `k`, base and tail alike. -/
def Gp (k : Nat) : Int :=
  ((3*(k/5) : Nat) : Int) + (if k%5=0 then 0 else if k%5=1 ∨ k%5=3 then 1 else 2)

/-- Row-one value at index `k`. -/
def Gq (k : Nat) : Int := if k%5=0 then 0 else if k%5=2 then 2 else 1

theorem getD_T (m k : Nat) (hk : k<m) : (T m).getD k (0,0)=(p k,q k) := by
  unfold T
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem getD_L_tail (m k : Nat) : (L m).getD (k+5) (0,0)=(T m).getD k (0,0) := by
  show (((0,0)::(1,1)::(2,2)::(1,1)::(2,1)::T m : Trans.Recal.PS)).getD (k+5) (0,0)
    =(T m).getD k (0,0)
  rw [show k+5=k+1+1+1+1+1 by omega]
  simp only [List.getD_cons_succ]

theorem p_eq_Gp (k : Nat) : p k=Gp (k+5) := by
  unfold p Gp
  rw [show (k+5)%5=k%5 by omega,show (k+5)/5=k/5+1 by omega]
  by_cases h0 : k%5=0
  · rw [if_pos h0,if_pos h0]
    push_cast
    omega
  · rw [if_neg h0,if_neg h0]
    by_cases h1 : k%5=1 ∨ k%5=3
    · rw [if_pos h1,if_pos h1]
      push_cast
      omega
    · rw [if_neg h1,if_neg h1]
      push_cast
      omega

theorem q_eq_Gq (k : Nat) : q k=Gq (k+5) := by
  unfold q Gq
  rw [show (k+5)%5=k%5 by omega]

theorem gp0_L (m k : Nat) (hk : k<m+5) : Trans.Recal.gp0 (L m) ((k:Nat):Int)=Gp k := by
  show (if (((k:Nat):Int)<0) then 0 else ((L m).getD k (0,0)).1)=Gp k
  rw [if_neg (by omega)]
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | (j+5), h =>
    rw [getD_L_tail,getD_T m j (by omega)]
    exact p_eq_Gp j

theorem gp1_L (m k : Nat) (hk : k<m+5) : Trans.Recal.gp1 (L m) ((k:Nat):Int)=Gq k := by
  show (if (((k:Nat):Int)<0) then 0 else ((L m).getD k (0,0)).2)=Gq k
  rw [if_neg (by omega)]
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | (j+5), h =>
    rw [getD_L_tail,getD_T m j (by omega)]
    exact q_eq_Gq j

/-! ### The parent rule, as arithmetic on `Gp`. -/

theorem Gp_val (a r : Nat) (hr : r<5) :
    Gp (5*a+r)=((3*a : Nat) : Int)+(if r=0 then 0 else if r=1 ∨ r=3 then 1 else 2) := by
  unfold Gp
  rw [show (5*a+r)/5=a by omega,show (5*a+r)%5=r by omega]

theorem Gp_lt_step (k : Nat) (hk : 1 ≤ k) (h : k%5 ≠ 3) : Gp (k-1)<Gp k := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<5 ∧ k=5*a+r := ⟨k/5,k%5,by omega,by omega⟩
  rw [show (5*a+r)%5=r by omega] at h
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=4 by omega) with rfl|rfl|rfl|rfl
  · obtain ⟨b,rfl⟩ : ∃ b, a=b+1 := ⟨a-1,by omega⟩
    rw [show 5*(b+1)+0-1=5*b+4 by omega,show 5*(b+1)+0=5*(b+1)+0 from rfl,
      Gp_val b 4 (by omega),Gp_val (b+1) 0 (by omega)]
    push_cast
    omega
  · rw [show 5*a+1-1=5*a+0 by omega,Gp_val a 0 (by omega),Gp_val a 1 (by omega)]
    omega
  · rw [show 5*a+2-1=5*a+1 by omega,Gp_val a 1 (by omega),Gp_val a 2 (by omega)]
    omega
  · rw [show 5*a+4-1=5*a+3 by omega,Gp_val a 3 (by omega),Gp_val a 4 (by omega)]
    omega

theorem Gp_three (k : Nat) (h : k%5=3) :
    Gp (k-3)<Gp k ∧ Gp k ≤ Gp (k-2) ∧ Gp k ≤ Gp (k-1) := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<5 ∧ k=5*a+r := ⟨k/5,k%5,by omega,by omega⟩
  rw [show (5*a+r)%5=r by omega] at h
  subst h
  rw [show 5*a+3-3=5*a+0 by omega,show 5*a+3-2=5*a+1 by omega,
    show 5*a+3-1=5*a+2 by omega,Gp_val a 0 (by omega),Gp_val a 1 (by omega),
    Gp_val a 2 (by omega),Gp_val a 3 (by omega)]
  refine ⟨by omega,by omega,by omega⟩

#guard (List.range 8).all fun m => Trans.Recal.trMax (L m)==2
#guard (List.range 40).all fun k =>
  (k=0) || (if k%5=3 then decide (Gp (k-3)<Gp k) else decide (Gp (k-1)<Gp k))
#guard (List.range 15).all fun m =>
  (List.range (m+5)).all fun k => Trans.Recal.gp0 (L m) ((k:Nat):Int)==Gp k
#guard (List.range 15).all fun m =>
  (List.range (m+5)).all fun k => Trans.Recal.gp1 (L m) ((k:Nat):Int)==Gq k
-- 行 0 の親は一様: k%5=3 なら k-3、それ以外は k-1
#guard (List.range 15).all fun m => (List.range (m+5)).all fun k =>
  Trans.Recal.fpar (L m) 0 ((k:Nat):Int) 0
    == (if k=0 then -1 else if k%5=3 then ((k:Int)-3) else ((k:Int)-1))

/-! ### Link 2, step 5: the row-zero parent, in closed form. -/

/-- 行 0 の親。`k%5=3` のときだけ 3 つ戻り、それ以外は 1 つ戻る。 -/
def parL (k : Nat) : Int :=
  if k=0 then -1 else if k%5=3 then ((k:Int)-3) else ((k:Int)-1)

theorem fpar0Aux_step (M : Trans.Recal.PS) (f : Nat) (tgt j0 kk : Int) :
    Trans.Recal.fpar0Aux (f+1) M tgt j0 kk
      = if j0<kk then -1 else if Trans.Recal.gp0 M j0<tgt then j0
        else Trans.Recal.fpar0Aux f M tgt (j0-1) kk := rfl

theorem fpar_L_zero (m k : Nat) (hk : k<m+5) :
    Trans.Recal.fpar (L m) 0 ((k:Nat):Int) 0=parL k := by
  unfold Trans.Recal.fpar parL
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((0:Nat)==0)=true from rfl,if_true]
  rw [length_L]
  by_cases h0 : k=0
  · subst h0
    rw [if_pos rfl]
    show Trans.Recal.fpar0Aux (m+5+1) (L m) (Trans.Recal.gp0 (L m) ((0:Nat):Int))
      (((0:Nat):Int)-1) 0=-1
    rw [show m+5+1=(m+5)+1 from rfl,fpar0Aux_step,if_pos (by omega)]
  · rw [if_neg h0]
    show Trans.Recal.fpar0Aux (m+5+1) (L m) (Trans.Recal.gp0 (L m) ((k:Nat):Int))
      (((k:Nat):Int)-1) 0=_
    rw [gp0_L m k hk]
    by_cases h3 : k%5=3
    · rw [if_pos h3]
      obtain ⟨hlt,hle2,hle1⟩ := Gp_three k h3
      have hk3 : 3 ≤ k := by omega
      have c1 : ¬(((k:Nat):Int)-1<0) := by omega
      have e1 : ((k:Nat):Int)-1=(((k-1:Nat)):Int) := by omega
      have c2 : ¬(Gp (k-1)<Gp k) := by omega
      have e2 : (((k-1:Nat)):Int)-1=(((k-2:Nat)):Int) := by omega
      have c3 : ¬((((k-2:Nat)):Int)<0) := by omega
      have c4 : ¬(Gp (k-2)<Gp k) := by omega
      have e3 : (((k-2:Nat)):Int)-1=(((k-3:Nat)):Int) := by omega
      have c5 : ¬((((k-3:Nat)):Int)<0) := by omega
      have e4 : (((k-3:Nat)):Int)=(k:Int)-3 := by omega
      rw [show m+5+1=(m+3)+1+1+1 by omega,fpar0Aux_step,if_neg c1,e1,
        gp0_L m (k-1) (by omega),if_neg c2,fpar0Aux_step,e2,if_neg c3,
        gp0_L m (k-2) (by omega),if_neg c4,fpar0Aux_step,e3,if_neg c5,
        gp0_L m (k-3) (by omega),if_pos hlt,e4]
    · rw [if_neg h3]
      have hk1 : 1 ≤ k := by omega
      have hlt := Gp_lt_step k hk1 h3
      have c1 : ¬(((k:Nat):Int)-1<0) := by omega
      have e1 : ((k:Nat):Int)-1=(((k-1:Nat)):Int) := by omega
      have e2 : (((k-1:Nat)):Int)=(k:Int)-1 := by omega
      rw [show m+5+1=(m+5)+1 from rfl,fpar0Aux_step,if_neg c1,e1,
        gp0_L m (k-1) (by omega),if_pos hlt,e2]

#guard (List.range 15).all fun m => (List.range (m+5)).all fun k =>
  Trans.Recal.fpar (L m) 0 ((k:Nat):Int) 0 == parL k

/-! ### Link 2, step 6: the ladder is principal, and it is one block.

Both come from `Rows/Ladder.lean`'s general lemmas: the only input is the row-zero
parent chain, which step 5 computed. -/

/-- The parent as a `Nat` index. -/
def parN (k : Nat) : Nat := if k%5=3 then k-3 else k-1

theorem parL_eq (k : Nat) (hk : 1 ≤ k) : parL k=((parN k : Nat) : Int) := by
  unfold parL parN
  rw [if_neg (by omega)]
  by_cases h3 : k%5=3
  · rw [if_pos h3,if_pos h3]
    omega
  · rw [if_neg h3,if_neg h3]
    omega

theorem parN_lt (k : Nat) (hk : 1 ≤ k) : parN k<k := by
  unfold parN
  by_cases h3 : k%5=3
  · rw [if_pos h3]; omega
  · rw [if_neg h3]; omega

theorem chain_L (m : Nat) : ∀ k, 1 ≤ k → k<(L m).length →
    Trans.Recal.fpar (L m) 0 ((k:Nat):Int) 0=((parN k : Nat) : Int) := by
  intro k hk1 hk
  rw [length_L] at hk
  rw [fpar_L_zero m k hk,parL_eq k hk1]

theorem chain_L_lt (m : Nat) : ∀ k, 1 ≤ k → k<(L m).length → parN k<k :=
  fun k hk1 _ => parN_lt k hk1

theorem chain_L_zero (m : Nat) : Trans.Recal.fpar (L m) 0 ((0:Nat):Int) 0=-1 := by
  rw [fpar_L_zero m 0 (by omega)]
  unfold parL
  rw [if_pos rfl]

theorem isPrincipalP_L (m : Nat) : Trans.Recal.isPrincipalP (L m)=true :=
  Rows.Ladder.isPrincipalP_of_chain (chain_L m) (chain_L_lt m) (chain_L_zero m)
    (by rw [length_L]; omega)

theorem ppair_L (m : Nat) : Trans.Recal.ppair (L m)=[L m] :=
  Rows.Ladder.ppair_of_chain (chain_L m) (chain_L_lt m) (chain_L_zero m)
    (by rw [length_L]; omega)

#guard (List.range 12).all fun m => Trans.Recal.isPrincipalP (L m)
#guard (List.range 12).all fun m => !(Trans.Recal.isZeroP (L m))
#guard (List.range 12).all fun m => Trans.Recal.ppair (L m)==[L m]

/-! ### Link 2, step 7: the single branch, and its own parent chain. -/

/-- The ladder below `trMax`, i.e. the one branch `brF` returns. -/
def V (m : Nat) : Trans.Recal.PS := (L m).drop 3

theorem length_V (m : Nat) : (V m).length=m+2 := by
  unfold V
  rw [List.length_drop,length_L]
  omega

theorem getD_drop {α : Type} [Inhabited α] (l : List α) (n j : Nat) (d : α) :
    (l.drop n).getD j d=l.getD (n+j) d := by
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem gp0_V (m j : Nat) (hj : j<m+2) :
    Trans.Recal.gp0 (V m) ((j:Nat):Int)=Gp (j+3) := by
  have h := gp0_L m (j+3) (by omega)
  rw [show Trans.Recal.gp0 (L m) ((j+3:Nat):Int)
      = (if (((j+3:Nat):Int)<0) then 0 else ((L m).getD (j+3) (0,0)).1) from rfl,
    if_neg (by omega)] at h
  show (if (((j:Nat):Int)<0) then 0 else ((V m).getD j (0,0)).1)=Gp (j+3)
  rw [if_neg (by omega)]
  unfold V
  rw [getD_drop,show 3+j=j+3 by omega]
  exact h

/-- The branch's own parent: three back when the index is a multiple of five. -/
def parV (j : Nat) : Nat := if j%5=0 then j-3 else j-1

theorem parV_lt (j : Nat) (hj : 1 ≤ j) : parV j<j := by
  unfold parV
  by_cases h : j%5=0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem gap_V_drop (j : Nat) (hj : 1 ≤ j) : Gp (parV j+3)<Gp (j+3) := by
  unfold parV
  by_cases h : j%5=0
  · rw [if_pos h,show j-3+3=j by omega]
    have := (Gp_three (j+3) (by omega)).1
    rwa [show j+3-3=j by omega] at this
  · rw [if_neg h,show j-1+3=j+2 by omega]
    have := Gp_lt_step (j+3) (by omega) (by omega)
    rwa [show j+3-1=j+2 by omega] at this

theorem gap_V_keep (j i : Nat) (hj : 1 ≤ j) (h1 : parV j<i) (h2 : i<j) :
    Gp (j+3) ≤ Gp (i+3) := by
  unfold parV at h1
  by_cases h : j%5=0
  · rw [if_pos h] at h1
    obtain ⟨_,hle2,hle1⟩ := Gp_three (j+3) (by omega)
    rw [show j+3-2=j+1 by omega] at hle2
    rw [show j+3-1=j+2 by omega] at hle1
    rcases (show i=j-2 ∨ i=j-1 by omega) with rfl|rfl
    · rw [show j-2+3=j+1 by omega]; exact hle2
    · rw [show j-1+3=j+2 by omega]; exact hle1
  · rw [if_neg h] at h1
    omega

theorem fpar_V_zero (m : Nat) : ∀ j, 1 ≤ j → j<(V m).length →
    Trans.Recal.fpar (V m) 0 ((j:Nat):Int) 0=((parV j : Nat) : Int) :=
  Rows.Ladder.fpar_of_gap
    (fun k hk => by rw [length_V] at hk; exact gp0_V m k hk)
    (fun k hk1 _ => parV_lt k hk1)
    (fun k hk1 _ => gap_V_drop k hk1)
    (fun k i hk1 _ h1 h2 => gap_V_keep k i hk1 h1 h2)

theorem fpar_V_root (m : Nat) : Trans.Recal.fpar (V m) 0 ((0:Nat):Int) 0=-1 :=
  Rows.Ladder.fpar_zero_of_gap
    (G := fun k => Gp (k+3))
    (fun k hk => by rw [length_V] at hk; exact gp0_V m k hk)
    (by rw [length_V]; omega)

theorem ppair_V (m : Nat) : Trans.Recal.ppair (V m)=[V m] :=
  Rows.Ladder.ppair_of_chain (fpar_V_zero m) (fun k hk1 _ => parV_lt k hk1)
    (fpar_V_root m) (by rw [length_V]; omega)

theorem brF_L (m : Nat) : Trans.Recal.brF (L m)=[V m] := by
  unfold Trans.Recal.brF
  rw [trMax_L]
  show Trans.Recal.ppair ((L m).drop 3)=_
  exact ppair_V m

theorem firstNodes_L (m : Nat) :
    Trans.Recal.firstNodes (L m)=[3,(((m+5:Nat)):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L,trMax_L]
  simp only [List.foldl_cons,List.foldl_nil,length_V]
  rw [show ([0]++[0+(((m+2:Nat)):Int)] : List Int)=[0,0+(((m+2:Nat)):Int)] from rfl]
  simp only [List.map_cons,List.map_nil]
  rw [show (2:Int)+1+0=3 from by omega,
    show (2:Int)+1+(0+(((m+2:Nat)):Int))=(((m+5:Nat)):Int) from by omega]

theorem joints_L (m : Nat) : Trans.Recal.joints (L m)=[0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_L]
  show [Trans.Recal.fpar (L m) 0 3 0]=[0]
  rw [show (3:Int)=((3:Nat):Int) from rfl,fpar_L_zero m 3 (by omega)]
  unfold parL
  rw [if_neg (by omega),if_pos (by omega),
    show ((3:Nat):Int)-3=0 from by omega]

#guard (List.range 12).all fun m => Trans.Recal.firstNodes (L m)==[3,(((m+5:Nat)):Int)]
#guard (List.range 12).all fun m => Trans.Recal.joints (L m)==[0]
#guard (List.range 12).all fun m => Trans.Recal.brF (L m)==[V m]
#guard (List.range 12).all fun m => Trans.Recal.ppair (V m)==[V m]

/-! ### Link 2, step 8: the first level of `red`. -/

theorem fpar0_eq (M : Trans.Recal.PS) (j k : Int) :
    Trans.Recal.fpar0 M j k=Trans.Recal.fpar M 0 j k := rfl

theorem fpar1_L_three_zero (m : Nat) : Trans.Recal.fpar (L m) 1 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 3 0
    if j1<0 then -1 else if Trans.Recal.gp1 (L m) j1<Trans.Recal.gp1 (L m) 3 then j1
    else Trans.Recal.fpar1Aux (m+5) (L m) (Trans.Recal.gp1 (L m) 3) j1 0)=0
  rw [show Trans.Recal.fpar0 (L m) 3 0=0 from by
    have h := fpar_L_zero m 3 (by omega)
    unfold parL at h
    rw [if_neg (by omega),if_pos (by omega)] at h
    rw [fpar0_eq,show ((3:Int))=((3:Nat):Int) from rfl,h]
    omega]
  rw [if_neg (by omega),
    show Trans.Recal.gp1 (L m) 0=0 from by
      rw [show ((0:Int))=((0:Nat):Int) from rfl,gp1_L m 0 (by omega)]; rfl,
    show Trans.Recal.gp1 (L m) 3=1 from by
      rw [show ((3:Int))=((3:Nat):Int) from rfl,gp1_L m 3 (by omega)]; rfl,
    if_pos (by omega)]

theorem V_cons (m : Nat) : V m=((1:Int),(1:Int)) :: (V m).drop 1 := by
  unfold V L
  rfl

theorem L_cons_V (m : Nat) :
    L m=([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))] : Trans.Recal.PS)++V m := by
  unfold V L
  rfl

theorem isZeroP_L (m : Nat) : Trans.Recal.isZeroP (L m)=false := by
  unfold Trans.Recal.isZeroP
  rw [show ((L m).length==1)=false from by rw [length_L]; simp]
  rfl

theorem gp0_L_zero (m : Nat) : Trans.Recal.gp0 (L m) 0=0 := by
  rw [show ((0:Int))=((0:Nat):Int) from rfl,gp0_L m 0 (by omega)]
  rfl

theorem gp1_L_zero (m : Nat) : Trans.Recal.gp1 (L m) 0=0 := by
  rw [show ((0:Int))=((0:Nat):Int) from rfl,gp1_L m 0 (by omega)]
  rfl

theorem gp1_V_zero (m : Nat) : Trans.Recal.gp1 (V m) 0=1 := by
  rw [show ((0:Int))=((0:Nat):Int) from rfl]
  show (if (((0:Nat):Int)<0) then 0 else ((V m).getD 0 (0,0)).2)=1
  rw [if_neg (by omega)]
  unfold V L
  rfl

/-- `red` の第 1 段。梯子は 3 列を切り出して、残りを 1 つの枝として再帰する。 -/
theorem red_L_step (m f : Nat) :
    Trans.Recal.red (f+1) (L m)
      = ([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))] : Trans.Recal.PS)
        ++ Trans.Recal.red f (V m) := by
  simp only [Trans.Recal.red]
  rw [isZeroP_L]
  simp only [Bool.false_eq_true,if_false]
  rw [isPrincipalP_L]
  simp only [if_true]
  rw [gp0_L_zero,gp1_L_zero]
  rw [if_pos (by rfl)]
  rw [trMax_L,lenI_L,
    show ((2:Int)==(m:Int)+5-1)=false from beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L,firstNodes_L,joints_L]
  simp only [List.length_cons,List.length_nil,List.range_succ,List.range_zero,
    List.foldl_cons,List.foldl_nil,List.nil_append,List.getD_cons_zero]
  rw [gp1_V_zero,show ((1:Int)==0)=false from by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_L_three_zero]
  rw [show Trans.Recal.jjSeq 0 2
      =([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))] : Trans.Recal.PS) from rfl]
  simp only [Trans.Recal.derp]
  rw [show ((0:Int)+1,(0:Int)+1) :: (V m).drop 1=V m from by
    rw [show ((0:Int)+1)=(1:Int) from by omega]
    exact (V_cons m).symm]
  rw [show (0:Int)-0=0 from by omega]
  rw [show Trans.Recal.incrFirst (Trans.Recal.red f (V m)) 0
      =Trans.Recal.red f (V m) from by
    unfold Trans.Recal.incrFirst
    rw [show (fun c : Int × Int => (c.1+0,c.2))=id from by
      funext c
      show (c.1+0,c.2)=c
      rw [Int.add_zero]]
    exact List.map_id _]

#guard (List.range 10).all fun m => Trans.Recal.fpar (L m) 1 3 0==0
#guard (List.range 10).all fun m =>
  L m==(([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))] : Trans.Recal.PS)++V m)
#guard Trans.Recal.jjSeq 0 2==([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))]
  : Trans.Recal.PS)
-- 第 1 段の後に残るのは `red (V m) = V m` だけ (測定)
#guard (List.range 10).all fun m => Trans.Recal.redP (V m)==V m

/-! ### Link 2, step 9: every ladder in the recursion is a WINDOW of one sequence.

`red` walks through a family of ladders; all of them are the same doubly-infinite
sequence `(Gp, Gq)` read from some offset, with the row-zero values shifted. -/

theorem Gp_add_five (k : Nat) : Gp (k+5)=Gp k+3 := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<5 ∧ k=5*a+r := ⟨k/5,k%5,by omega,by omega⟩
  rw [show 5*a+r+5=5*(a+1)+r by omega,Gp_val (a+1) r hr,Gp_val a r hr]
  push_cast
  omega

theorem Gq_add_five (k : Nat) : Gq (k+5)=Gq k := by
  unfold Gq
  rw [show (k+5)%5=k%5 by omega]

/-- The ladder read from offset `i`, shifted by `d`, of length `n`. -/
def Win (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS :=
  (List.range n).map fun j => (Gp (j+i)+d,Gq (j+i))

theorem length_Win (i : Nat) (d : Int) (n : Nat) : (Win i d n).length=n := by
  simp [Win]

theorem Win_succ (i : Nat) (d : Int) (n : Nat) :
    Win i d (n+1)=Win i d n++[(Gp (n+i)+d,Gq (n+i))] := by
  unfold Win
  rw [List.range_succ,List.map_append]
  rfl

/-- Reading five later is a shift of three. -/
theorem Win_add_five (i : Nat) (d : Int) (n : Nat) : Win (i+5) d n=Win i (d+3) n := by
  unfold Win
  apply List.map_congr_left
  intro j _
  show (Gp (j+(i+5))+d,Gq (j+(i+5)))=(Gp (j+i)+(d+3),Gq (j+i))
  rw [show j+(i+5)=(j+i)+5 by omega,Gp_add_five,Gq_add_five]
  congr 1
  omega

/-- Dropping a column advances the offset. -/
theorem Win_drop (i : Nat) (d : Int) (n : Nat) : (Win i d (n+1)).drop 1=Win (i+1) d n := by
  unfold Win
  rw [List.range_succ_eq_map,List.map_cons,List.drop_succ_cons,List.drop_zero,
    List.map_map]
  apply List.map_congr_left
  intro j _
  show (Gp (j+1+i)+d,Gq (j+1+i))=(Gp (j+(i+1))+d,Gq (j+(i+1)))
  rw [show j+1+i=j+(i+1) by omega]

theorem incrFirst_Win (i : Nat) (d e : Int) (n : Nat) :
    Trans.Recal.incrFirst (Win i d n) e=Win i (d+e) n := by
  unfold Trans.Recal.incrFirst Win
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  show ((Gp (j+i)+d)+e,Gq (j+i))=(Gp (j+i)+(d+e),Gq (j+i))
  rw [Int.add_assoc]

theorem L_eq_Win (m : Nat) : L m=Win 0 0 (m+5) := by
  unfold Win
  have : ∀ n : Nat, (List.range n).map (fun j => (Gp (j+0)+(0:Int),Gq (j+0)))
      =(List.range n).map (fun j => (Gp j,Gq j)) := by
    intro n
    apply List.map_congr_left
    intro j _
    show (Gp (j+0)+(0:Int),Gq (j+0))=(Gp j,Gq j)
    rw [Nat.add_zero,Int.add_zero]
  rw [this]
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show m+1+5=(m+5)+1 by omega,List.range_succ,List.map_append,← ih,
      show L (m+1)=L m++[(p m,q m)] from L_succ m]
    congr 1
    show [(p m,q m)]=[(Gp (m+5),Gq (m+5))]
    rw [← p_eq_Gp,← q_eq_Gq]

theorem V_eq_Win (m : Nat) : V m=Win 3 0 (m+2) := by
  unfold V
  rw [L_eq_Win]
  have : (m+5)=(m+2)+3 := by omega
  rw [this]
  clear this
  induction (m+2) with
  | zero => rfl
  | succ n ih =>
    rw [show n+1+3=(n+3)+1 by omega,Win_succ,List.drop_append_of_le_length (by
      rw [length_Win]; omega),ih,Win_succ]

#guard (List.range 10).all fun m => L m==Win 0 0 (m+5)
#guard (List.range 10).all fun m => V m==Win 3 0 (m+2)
#guard (List.range 8).all fun n => (List.range 6).all fun i => Win (i+5) 0 n==Win i 3 n
#guard (List.range 8).all fun n => (List.range 6).all fun i =>
  (Win i 0 (n+1)).drop 1==Win (i+1) 0 n
-- `red` は shift を忘れる: 正規形は (i mod 5, n) だけで決まる (測定)
#guard (List.range 5).all fun i => (List.range 4).all fun n =>
  Trans.Recal.redP (((2:Int),(1:Int)) :: Win (i+5) 1 n)
    == Trans.Recal.redP (((5:Int),(1:Int)) :: Win (i+5) 3 n)

/-! ### Link 2, step 10: the five normal forms

`red` normalises a ladder `(c,1) :: Win i d n` to something that depends only on
`i mod 5` and `n` — the head value `c` and the shift `d` are forgotten (measured over
`c ∈ 2..4`, `d ∈ 0..3`; the forgetting is not unconditional, see the `#guard`s).

FOUR OF THE FIVE NORMAL FORMS ARE A HEAD PLUS A WINDOW.  Phase 2 is the exception and
carries a SECOND exceptional column, which is why a uniform closed form was not found by
guessing and had to be read off the five cases:

    NF 0 n = (1,1) :: Win 0 2 n
    NF 1 n = (1,1) :: Win 1 1 n
    NF 2 n = (1,1) :: (2,2) :: Win 3 1 (n-1)        ← two heads
    NF 3 n = (1,1) :: Win 3 1 n
    NF 4 n = (1,1) :: Win 4 0 n

`NF` is a fixed point of `redP` (measured), which is the statement `redP_L` will consume:
`red (V m) = V m` reduces to `red (Y 2 5 1 m) = NF 0 m`, and the induction that proves it
walks the five phases with `n` decreasing. -/

/-- The shape every level of `red`'s recursion has: one exceptional head over a window. -/
def Y (c : Int) (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS := (c,1) :: Win i d n

/-- The normal form of `Y`, by phase and length. -/
def NF : Nat → Nat → Trans.Recal.PS
  | 0, n => ((1:Int),(1:Int)) :: Win 0 2 n
  | 1, n => ((1:Int),(1:Int)) :: Win 1 1 n
  | 2, 0 => [((1:Int),(1:Int))]
  | 2, n+1 => ((1:Int),(1:Int)) :: ((2:Int),(2:Int)) :: Win 3 1 n
  | 3, n => ((1:Int),(1:Int)) :: Win 3 1 n
  | _, n => ((1:Int),(1:Int)) :: Win 4 0 n

-- 相ごとの正規形 (測定)
#guard (List.range 5).all fun r => (List.range 14).all fun n =>
  Trans.Recal.redP (Y 2 (r+5) 1 n)==NF r n
-- オフセットは 5 で巡回する
#guard (List.range 5).all fun r => (List.range 10).all fun n =>
  (List.range 3).all fun a => Trans.Recal.redP (Y 2 (r+5*(a+1)) 1 n)==NF r n
-- 正規形は不動点
#guard (List.range 5).all fun r => (List.range 12).all fun n =>
  Trans.Recal.redP (NF r n)==NF r n
-- 頭と shift を忘れるのは無条件ではない: 成り立つ範囲を記録しておく
#guard ([(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)] : List (Nat × Int)).all fun cd =>
  (List.range 5).all fun r => (List.range 8).all fun n =>
    Trans.Recal.redP (Y ((cd.1:Nat):Int) (r+5) cd.2 n)==NF r n

/-! ### Link 2, step 11: the phase transition table

The recursion alternates between two shapes, and their normal forms are linked:

    Y c i d n = (c,1) :: Win i d n              redP (Y 2 (r+5) 1 n) = NF r n
    A c i d n = (0,0) :: Y c i d n              redP (A 2 (r+5) 1 n) = (0,0) :: NF r n

`red (Y …)` goes through `red (A …)` and strips the leading `(0,0)` with a zero shift, so
the whole recursion is carried by `red (A …)`, whose fold descends one phase and one column:

    phase r    trMax   joints    brF     nJ    NJ                      shift
      0          1      [1]       1      -1    (2,0) :: Win (i+1) d (n-1)   2
      1          1      [1]/[1,1] 1/2     0    …                            1
      2          2      []/[1]    0/1     1    …                            0
      3          1      [1]       1       0    (2,1) :: Win (i+1) d (n-1)   1
      4          1      [1]       1       0    (2,1) :: Win (i+1) d (n-1)   1

**PHASES 3 AND 4 CLOSE ON THE WINDOW ALGEBRA ALONE**, and the two identities that make
them close are worth writing down because they are the reason the shift is 1:

    (2,1) :: Win 4 1 (n-1) = Win 3 1 n            phase 3
    (2,1) :: Win 0 3 (n-1) = Win 4 0 n            phase 4, through Win 5 0 = Win 0 3

**PHASES 0, 1 AND 2 DO NOT.**  Phase 0's `NJ` has row-one `0`, not `1`, so it leaves the
`Y` family; phase 1's branch SPLITS in two once `n ≥ 2`; phase 2 has `trMax = 2`.  Those
three are what remain of link 2, and the reason they are harder is the row-one value `2`
this family carries — `Rows/G10.lean`'s ladders never exceed `1`. -/

-- A 族の正規形 (測定)
#guard (List.range 5).all fun r => (List.range 12).all fun n =>
  Trans.Recal.redP (((0:Int),(0:Int)) :: Y 2 (r+5) 1 n)==(((0:Int),(0:Int)) :: NF r n)
/-- 窓の先頭を切り出す。 -/
theorem Win_cons (i : Nat) (d : Int) (n : Nat) :
    Win i d (n+1)=(Gp i+d,Gq i) :: Win (i+1) d n := by
  unfold Win
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  · rw [Nat.zero_add]
  · apply List.map_congr_left
    intro j _
    show (Gp (j+1+i)+d,Gq (j+1+i))=(Gp (j+(i+1))+d,Gq (j+(i+1)))
    rw [show j+1+i=j+(i+1) by omega]

/-- 相 3 が閉じる等式。 -/
theorem phase3_cons (n : Nat) :
    ((2:Int),(1:Int)) :: Win 4 1 n=Win 3 1 (n+1) := by
  rw [Win_cons]
  rfl

/-- 相 4 が閉じる等式。`Win 5 0 = Win 0 3` を経由する。 -/
theorem phase4_cons (n : Nat) :
    ((2:Int),(1:Int)) :: Win 0 3 n=Win 4 0 (n+1) := by
  rw [Win_cons,show Win (4+1) 0 n=Win 0 3 n from by
    rw [show (4+1)=(0+5) by omega,Win_add_five]
    rfl]
  rfl

-- 相 3・相 4 が閉じる 2 つの等式
#guard (List.range 12).all fun n =>
  (((2:Int),(1:Int)) :: Win 4 1 n)==Win 3 1 (n+1)
#guard (List.range 12).all fun n =>
  (((2:Int),(1:Int)) :: Win 0 3 n)==Win 4 0 (n+1)

/-! ### Link 2, step 12: the third family, and where the row-one `2` bites

Phase 0's descendant has row-one `0`, so the recursion leaves `Y` for

    Z c i d n = (c,0) :: Win i d n

and phase 0 closes exactly when `red (Z 2 6 1 n) = (0,0) :: Win 1 0 n`, which is measured.
`Z`'s normal forms are windows in three phases and not in the fourth:

    NFZ 1 n = (0,0) :: Win 1 0 n
    NFZ 3 n = (0,0) :: Win 3 0 n
    NFZ 4 n = (0,0) :: Win 4 (-1) n
    NFZ 2 n = (0,0) :: (1,1) :: (1,1) :: …        ← a DOUBLED column, not a window

**PHASE 2 IS THE EXCEPTION IN EVERY FAMILY.**  `NF 2` carries a second head, `NFZ 2`
carries a doubled column, phase 2 is the one with `trMax = 2`, and phase 1 — the phase whose
branch reaches phase 2 — is the one whose branch splits.  All four are the same fact: `Gq 2`
is `2`, and this is the only row-one value above `1` in the ladder.  `Rows/G10.lean`'s
ladders never exceed `1`, which is why its six-phase cycle has no analogue of any of this. -/

-- 相 0 が閉じる条件 (測定)
#guard (List.range 12).all fun n =>
  Trans.Recal.redP (((2:Int),(0:Int)) :: Win 6 1 n)==(((0:Int),(0:Int)) :: Win 1 0 n)
#guard (List.range 10).all fun n =>
  Trans.Recal.redP (((2:Int),(0:Int)) :: Win 8 1 n)==(((0:Int),(0:Int)) :: Win 3 0 n)
#guard (List.range 10).all fun n =>
  Trans.Recal.redP (((2:Int),(0:Int)) :: Win 9 1 n)==(((0:Int),(0:Int)) :: Win 4 (-1) n)
-- 相 2 は窓にならない: 3 列目が 2 列目と同じ
#guard Trans.Recal.redP (((2:Int),(0:Int)) :: Win 7 1 3)
  ==([((0:Int),(0:Int)),((1:Int),(1:Int)),((1:Int),(1:Int)),((2:Int),(1:Int))]
     : Trans.Recal.PS)

/-! ### Link 2, step 13: the `Z` step is a renormalisation, not a fold. -/

/-- 行 1 が 0 の頭を持つ梯子。相 0 の子孫。`Z` は Rathjen の記号なので `Zr`。 -/
def Zr (c : Int) (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS := (c,0) :: Win i d n

theorem length_Zr (c : Int) (i : Nat) (d : Int) (n : Nat) : (Zr c i d n).length=n+1 := by
  unfold Zr
  rw [List.length_cons,length_Win]

theorem gp0_Zr_zero (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (Zr c i d n) 0=c := by
  show (if ((0:Int)<0) then 0 else ((Zr c i d n).getD 0 (0,0)).1)=c
  rw [if_neg (by omega)]
  rfl

theorem gp1_Zr_zero (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (Zr c i d n) 0=0 := by
  show (if ((0:Int)<0) then 0 else ((Zr c i d n).getD 0 (0,0)).2)=0
  rw [if_neg (by omega)]
  rfl

theorem isZeroP_Zr (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.isZeroP (Zr c i d n)=false := by
  unfold Trans.Recal.isZeroP
  rw [show ((Zr c i d n).length==1)=false from by rw [length_Zr]; simp; omega]
  rfl

theorem incrFirst_Zr (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.incrFirst (Zr c i d n) (-c)=((0:Int),(0:Int)) :: Win i (d-c) n := by
  unfold Trans.Recal.incrFirst Zr
  rw [List.map_cons]
  congr 1
  · show ((c+(-c) : Int),(0:Int))=((0:Int),(0:Int))
    rw [show c+(-c)=(0:Int) from by omega]
  · show Trans.Recal.incrFirst (Win i d n) (-c)=_
    rw [incrFirst_Win,show d+(-c)=d-c from by omega]

/-- `Z` の段。頭の行 1 が 0 なので畳み込みではなく、頭を 0 に正規化して降りるだけ。 -/
theorem red_Zr_step (c : Int) (i : Nat) (d : Int) (n f : Nat) (hn : 1 ≤ n)
    (hc : (c==(0:Int))=false)
    (hprin : Trans.Recal.isPrincipalP (Zr c i d n)=true) :
    Trans.Recal.red (f+1) (Zr c i d n)
      = Trans.Recal.red f (((0:Int),(0:Int)) :: Win i (d-c) n) := by
  simp only [Trans.Recal.red]
  rw [isZeroP_Zr c i d n hn]
  simp only [Bool.false_eq_true,if_false]
  rw [hprin]
  simp only [if_true]
  rw [gp0_Zr_zero,gp1_Zr_zero,hc]
  simp only [Bool.false_and,Bool.false_eq_true,if_false]
  rw [show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [incrFirst_Zr]

#guard (List.range 6).all fun n => (List.range 5).all fun r =>
  Trans.Recal.redP (Zr 2 (r+5) 1 (n+1))
    == Trans.Recal.redP (((0:Int),(0:Int)) :: Win (r+5) (-1) (n+1))

/-! ### Link 2, step 14: the `Y` step goes through `A` and strips the head. -/

theorem incrFirst_zero (M : Trans.Recal.PS) : Trans.Recal.incrFirst M 0=M := by
  unfold Trans.Recal.incrFirst
  rw [show (fun c : Int × Int => (c.1+0,c.2))=id from by
    funext c
    show (c.1+0,c.2)=c
    rw [Int.add_zero]]
  exact List.map_id _

theorem length_Y (c : Int) (i : Nat) (d : Int) (n : Nat) : (Y c i d n).length=n+1 := by
  unfold Y
  rw [List.length_cons,length_Win]

theorem gp0_Y_zero (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (Y c i d n) 0=c := by
  show (if ((0:Int)<0) then 0 else ((Y c i d n).getD 0 (0,0)).1)=c
  rw [if_neg (by omega)]
  rfl

theorem gp1_Y_zero (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (Y c i d n) 0=1 := by
  show (if ((0:Int)<0) then 0 else ((Y c i d n).getD 0 (0,0)).2)=1
  rw [if_neg (by omega)]
  rfl

theorem isZeroP_Y (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.isZeroP (Y c i d n)=false := by
  unfold Trans.Recal.isZeroP
  rw [show (Trans.Recal.gp1 (Y c i d n) 0==0)=false from by
    rw [gp1_Y_zero]; rfl]
  simp

theorem incrFirst_Y (c : Int) (i : Nat) (d : Int) (n : Nat) (e : Int) :
    Trans.Recal.incrFirst (Y c i d n) e=Y (c+e) i (d+e) n := by
  unfold Trans.Recal.incrFirst Y
  rw [List.map_cons]
  congr 1
  show Trans.Recal.incrFirst (Win i d n) e=_
  rw [incrFirst_Win]

/-- `Y` の段。`A` の結果から頭の `(0,0)` を落とすだけ。ずらしは `0` になる。 -/
theorem red_Y_of_A (c : Int) (i : Nat) (d : Int) (n f : Nat) (W : Trans.Recal.PS)
    (hc : (c==(0:Int))=false)
    (hprin : Trans.Recal.isPrincipalP (Y c i d n)=true)
    (hA : Trans.Recal.red f (((0:Int),(0:Int)) :: Y (c+1) i (d+1) n)
      =((0:Int),(0:Int)) :: W)
    (hWlen : 1 ≤ W.length)
    (hWprin : Trans.Recal.isPrincipalP W=true)
    (hW : Trans.Recal.gp0 W 0=Trans.Recal.gp1 W 0) :
    Trans.Recal.red (f+1) (Y c i d n)=W := by
  have hNdrop : (((0:Int),(0:Int)) :: W).drop 1=W := rfl
  have hg0 : Trans.Recal.gp0 (((0:Int),(0:Int)) :: W) 1=Trans.Recal.gp0 W 0 := rfl
  have hg1 : Trans.Recal.gp1 (((0:Int),(0:Int)) :: W) 1=Trans.Recal.gp1 W 0 := rfl
  simp only [Trans.Recal.red]
  rw [isZeroP_Y]
  simp only [Bool.false_eq_true,if_false]
  rw [hprin]
  simp only [if_true]
  rw [gp0_Y_zero,gp1_Y_zero,hc]
  simp only [Bool.false_and,Bool.false_eq_true,if_false]
  rw [show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Recal.jjSeq 0 ((1:Int)-1)=[((0:Int),(0:Int))] from rfl,
    incrFirst_Y c i d n 1]
  show (let N := Trans.Recal.red f ([((0:Int),(0:Int))]++Y (c+1) i (d+1) n)
    let jN : Int := Trans.Recal.lenI N-1
    if decide ((1:Int) ≤ jN) && Trans.Recal.isPrincipalP (N.drop (1:Int).toNat) then
      Trans.Recal.incrFirst (N.drop (1:Int).toNat)
        (-(Trans.Recal.gp0 N 1)+Trans.Recal.gp1 N 1)
    else Y c i d n)=W
  rw [show ([((0:Int),(0:Int))]++Y (c+1) i (d+1) n)
      =((0:Int),(0:Int)) :: Y (c+1) i (d+1) n from rfl,hA]
  show (if decide ((1:Int) ≤ Trans.Recal.lenI (((0:Int),(0:Int)) :: W)-1)
      && Trans.Recal.isPrincipalP ((((0:Int),(0:Int)) :: W).drop 1) then
    Trans.Recal.incrFirst ((((0:Int),(0:Int)) :: W).drop 1)
      (-(Trans.Recal.gp0 (((0:Int),(0:Int)) :: W) 1)
        +Trans.Recal.gp1 (((0:Int),(0:Int)) :: W) 1)
    else Y c i d n)=W
  rw [hNdrop,hg0,hg1,hW,hWprin,
    show decide ((1:Int) ≤ Trans.Recal.lenI (((0:Int),(0:Int)) :: W)-1)=true from
      decide_eq_true (by
        unfold Trans.Recal.lenI
        rw [List.length_cons]
        omega)]
  simp only [Bool.and_self,if_true]
  rw [show -(Trans.Recal.gp1 W 0)+Trans.Recal.gp1 W 0=(0:Int) from by omega,
    incrFirst_zero]

-- `Y` の段が実際に効くことの確認 (測定)
#guard (List.range 5).all fun r => (List.range 8).all fun n =>
  Trans.Recal.redP (Y 2 (r+5) 1 n)==NF r n

/-! ### Link 3: the dictionary and the closed expansion sequence `fD`. -/
abbrev Z0t : Term := Z zero

theorem fD_isAP : ∀ n : Nat, (fD n).isAP=true
  | 0 => rfl
  | _+1 => rfl

theorem fD_toList : ∀ n : Nat, (fD n).toList=[fD n]
  | 0 => rfl
  | _+1 => rfl

theorem fD_bne_zero : ∀ n : Nat, ((fD n)==zero)=false
  | 0 => rfl
  | _+1 => rfl

theorem fD_bne_one : ∀ n : Nat, ((fD n)==one)=false
  | 0 => rfl
  | n+1 => by
    refine beq_eq_false_iff_ne.mpr ?_
    intro h
    have h' : phi (fD n) (plus Cps one)=phi zero zero := h
    injection h' with h1 _
    have hz : ((fD n)==zero)=true := beq_of_eq h1
    rw [fD_bne_zero n] at hz
    exact Bool.noConfusion hz

theorem fD_inT_lt : ∀ n : Nat, inT (fD n)=true ∧ lt (fD n) Z0t=true
  | 0 => ⟨by decide, by decide⟩
  | n+1 => by
    obtain ⟨hin,hlt⟩ := fD_inT_lt n
    have hltM : lt (fD n) TM.Term.M=true :=
      Evidence.WF.lt_trans_inT hin (by decide) (by decide) hlt (by decide)
    refine ⟨?_,?_⟩
    · show (inT (fD n) && inT (plus Cps one) && lt (fD n) TM.Term.M
        && lt (plus Cps one) TM.Term.M)=true
      rw [hin,hltM]
      rfl
    · show lt (phi (fD n) (plus Cps one)) Z0t=true
      unfold lt
      cases h:fuelOf (phi (fD n) (plus Cps one)) Z0t with
      | zero => simp [fuelOf] at h
      | succ f =>
        rw [Evidence.WF.ltF_succ_phi_Z]
        simp only [Bool.and_eq_true]
        have hf : (fD n).deg+Z0t.deg≤f := by
          unfold fuelOf at h
          simp only [Term.deg] at h ⊢
          omega
        have hg : (plus Cps one).deg+Z0t.deg≤f := by
          unfold fuelOf at h
          simp only [Term.deg] at h ⊢
          omega
        refine ⟨?_,?_⟩
        · rw [← Evidence.WF.lt_eq_ltF (fD n) Z0t f hf]
          exact hlt
        · rw [← Evidence.WF.lt_eq_ltF (plus Cps one) Z0t f hg]
          decide

theorem fD_inT (n : Nat) : inT (fD n)=true := (fD_inT_lt n).1
theorem fD_lt_Z0t (n : Nat) : lt (fD n) Z0t=true := (fD_inT_lt n).2

theorem fD_lt_Z1 (n : Nat) : lt (fD n) (Z one)=true :=
  Evidence.WF.lt_trans_inT (fD_inT n) (by decide) (by decide)
    (fD_lt_Z0t n) (by decide)

theorem le_fD_Z0t (n : Nat) : le (fD n) Z0t=true :=
  Evidence.WF.le_of_lt (fD_lt_Z0t n)

theorem toList_addZfD (n : Nat) : (add Z0t (fD n)).toList=[Z0t,fD n] := by
  change Z0t::(fD n).toList=_
  rw [fD_toList]

theorem plus_Z0t_fD (n : Nat) : plus Z0t (fD n)=add Z0t (fD n) := by
  unfold plus
  rw [show Z0t.toList=[Z0t] from rfl,fD_toList n]
  simp only [List.filter_cons,List.filter_nil,le_fD_Z0t n]
  rfl

theorem lt_M_addZfD (n : Nat) : lt TM.Term.M (add Z0t (fD n))=false := by
  unfold lt
  rw [show fuelOf TM.Term.M (add Z0t (fD n))=
      (2*(TM.Term.M.deg+(add Z0t (fD n)).deg)+6)+1+1 from by
        unfold fuelOf
        omega,
    Evidence.WF.ltF_succ_M_add]
  simp only [show ((TM.Term.M:Term)==Z0t)=false from rfl,Bool.false_or,
    Evidence.WF.ltF_succ_M_Z]

theorem omegaNF_addZfD (n : Nat) :
    omegaNF (add Z0t (fD n))=phi zero (add Z0t (fD n)) := by
  rw [omegaNF_of_le_M (lt_M_addZfD n)]
  exact Evidence.StageB.phiNF_add_pair rfl (fD_isAP n) (fD_bne_one n)

/-- 1 段目の崩壊。`Ω` が 1 つ入る。 -/
def Ct (n : Nat) : Term := phi zero (add Z0t (fD n))
/-- 2 段目の崩壊。**`Ω` は増えない** — 1 段目の値が既に `Ω` を超えるため。 -/
def Dt (n : Nat) : Term := phi zero (Ct n)

theorem collapse_one_fD (n : Nat) : Trans.Dict.collapse 1 (fD n)=Ct n := by
  have hw : Trans.Dict.wcnf (Z one) [fD n]=([],fD n) := by
    rw [Trans.Dict.wcnf,if_pos (fD_lt_Z1 n)]
    rfl
  unfold Trans.Dict.collapse
  rw [show Trans.Dict.reg (1+1)=Z one from rfl,
    show Trans.Dict.reg 1=Z0t from rfl,
    show ((1:Nat)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fD_toList n,hw]
  simp only [List.foldl_nil,Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left (fD_isAP n),plus_Z0t_fD n,omegaNF_addZfD n]
  rfl

theorem Ct_isAP (n : Nat) : (Ct n).isAP=true := rfl
theorem Ct_toList (n : Nat) : (Ct n).toList=[Ct n] := rfl

theorem Z0t_lt_Ct (n : Nat) : lt Z0t (Ct n)=true := by
  show lt Z0t (phi zero (add Z0t (fD n)))=true
  unfold lt
  cases h:fuelOf Z0t (phi zero (add Z0t (fD n))) with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_Z_phi]
    have hf : Z0t.deg+(add Z0t (fD n)).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [show ((Z0t==(zero:Term)))=false from rfl,
      show ((Z0t==add Z0t (fD n)))=false from rfl]
    simp only [Bool.false_or]
    rw [← Evidence.WF.lt_eq_ltF Z0t (add Z0t (fD n)) f hf,
      Evidence.WF.lt_atom_add (s := Z0t) rfl,Evidence.WF.le_self]
    simp only [Bool.or_true]

theorem inT_addZfD : ∀ n : Nat, inT (add Z0t (fD n))=true
  | 0 => by
    show (Z0t.isAP && inT Z0t && inT (fD 0) && ((fD 0).isAP && le (fD 0) Z0t))=true
    rw [fD_inT 0,fD_isAP 0,le_fD_Z0t 0]
    rfl
  | n+1 => by
    show (Z0t.isAP && inT Z0t && inT (fD (n+1))
      && ((fD (n+1)).isAP && le (fD (n+1)) Z0t))=true
    rw [fD_inT (n+1),fD_isAP (n+1),le_fD_Z0t (n+1)]
    rfl

/-- 和は非和と比べるとき先頭だけで決まる。 -/
theorem lt_addZfD (n : Nat) {u : Term} (h0 : u ≠ zero) (hn : Evidence.WF.NSum u=true)
    (hz : lt Z0t u=true) : lt (add Z0t (fD n)) u=true := by
  unfold lt
  cases h:fuelOf (add Z0t (fD n)) u with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_add_nsum f h0 hn]
    have hf : Z0t.deg+u.deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [← Evidence.WF.lt_eq_ltF Z0t u f hf]
    exact hz

theorem addZfD_lt_M (n : Nat) : lt (add Z0t (fD n)) TM.Term.M=true :=
  lt_addZfD n (by exact Term.noConfusion) rfl (by decide)

theorem addZfD_lt_Z1 (n : Nat) : lt (add Z0t (fD n)) (Z one)=true :=
  lt_addZfD n (by exact Term.noConfusion) rfl (by decide)

theorem Ct_inT (n : Nat) : inT (Ct n)=true := by
  show (inT zero && inT (add Z0t (fD n)) && lt zero TM.Term.M
    && lt (add Z0t (fD n)) TM.Term.M)=true
  rw [inT_addZfD n,addZfD_lt_M n]
  rfl

theorem Ct_lt_Z1 (n : Nat) : lt (Ct n) (Z one)=true := by
  show lt (phi zero (add Z0t (fD n))) (Z one)=true
  unfold lt
  cases h:fuelOf (phi zero (add Z0t (fD n))) (Z one) with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_phi_Z]
    simp only [Bool.and_eq_true]
    have h1 : (zero:Term).deg+(Z one).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    have h2 : (add Z0t (fD n)).deg+(Z one).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    refine ⟨?_,?_⟩
    · rw [← Evidence.WF.lt_eq_ltF zero (Z one) f h1]
      decide
    · rw [← Evidence.WF.lt_eq_ltF (add Z0t (fD n)) (Z one) f h2]
      exact addZfD_lt_Z1 n

theorem le_Ct_Z0t (n : Nat) : le (Ct n) Z0t=false := by
  unfold le
  rw [show ((Ct n)==Z0t)=false from beq_eq_false_iff_ne.mpr
    (Ne.symm (Evidence.WF.ne_of_ltF (Z0t_lt_Ct n)))]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (by decide) (Ct_inT n) (Z0t_lt_Ct n)

theorem plus_Z0t_Ct (n : Nat) : plus Z0t (Ct n)=Ct n := by
  unfold plus
  rw [show Z0t.toList=[Z0t] from rfl,Ct_toList n]
  simp only [List.filter_cons,List.filter_nil,le_Ct_Z0t n]
  rfl

theorem lt_M_Ct (n : Nat) : lt TM.Term.M (Ct n)=false := by
  show lt TM.Term.M (phi zero (add Z0t (fD n)))=false
  exact Rows.ProofsB.lt_M_phi _ _

theorem omegaNF_Ct (n : Nat) : omegaNF (Ct n)=Dt n := by
  rw [omegaNF_of_le_M (lt_M_Ct n)]
  show phiNF zero (phi zero (add Z0t (fD n)))=_
  exact Rows.ProofsB.phiNF_phi_arg (a := zero) rfl

theorem collapse_one_Ct (n : Nat) : Trans.Dict.collapse 1 (Ct n)=Dt n := by
  have hw : Trans.Dict.wcnf (Z one) [Ct n]=([],Ct n) := by
    rw [Trans.Dict.wcnf,if_pos (Ct_lt_Z1 n)]
    rfl
  unfold Trans.Dict.collapse
  rw [show Trans.Dict.reg (1+1)=Z one from rfl,
    show Trans.Dict.reg 1=Z0t from rfl,
    show ((1:Nat)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [Ct_toList n,hw]
  simp only [List.foldl_nil,Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left (Ct_isAP n),plus_Z0t_Ct n,omegaNF_Ct n]

#guard (List.range 5).all fun n => Trans.Dict.collapse 1 (fD n)==Ct n
#guard (List.range 5).all fun n => Trans.Dict.collapse 1 (Ct n)==Dt n

/-! ### 一段の合成 -/

theorem Dt_isAP (n : Nat) : (Dt n).isAP=true := rfl
theorem Dt_toList (n : Nat) : (Dt n).toList=[Dt n] := rfl

theorem Dt_inT (n : Nat) : inT (Dt n)=true := by
  show (inT zero && inT (Ct n) && lt zero TM.Term.M && lt (Ct n) TM.Term.M)=true
  rw [Ct_inT n,show lt (Ct n) TM.Term.M=true from rfl]
  rfl

theorem lt_Ct_Z0t (n : Nat) : lt (Ct n) Z0t=false :=
  Evidence.WF.lt_asymm_inT (by decide) (Ct_inT n) (Z0t_lt_Ct n)

/-- `Dt n` は `Ω` より大きい: `wcnf` の else 枝に落ちる。 -/
theorem lt_Dt_Z0t (n : Nat) : lt (Dt n) Z0t=false := by
  show lt (phi zero (Ct n)) Z0t=false
  unfold lt
  cases h:fuelOf (phi zero (Ct n)) Z0t with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_phi_Z]
    have hf : (Ct n).deg+Z0t.deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [← Evidence.WF.lt_eq_ltF (Ct n) Z0t f hf,lt_Ct_Z0t n]
    simp only [Bool.and_false]

theorem Dt_lt_Z1 (n : Nat) : lt (Dt n) (Z one)=true := by
  show lt (phi zero (Ct n)) (Z one)=true
  unfold lt
  cases h:fuelOf (phi zero (Ct n)) (Z one) with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_phi_Z]
    simp only [Bool.and_eq_true]
    have h1 : (zero:Term).deg+(Z one).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    have h2 : (Ct n).deg+(Z one).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    refine ⟨?_,?_⟩
    · rw [← Evidence.WF.lt_eq_ltF zero (Z one) f h1]
      decide
    · rw [← Evidence.WF.lt_eq_ltF (Ct n) (Z one) f h2]
      exact Ct_lt_Z1 n

theorem plus_Z1_Dt (n : Nat) : plus (Z one) (Dt n)=add (Z one) (Dt n) := by
  unfold plus
  rw [show (Z one).toList=[Z one] from rfl,Dt_toList n]
  simp only [List.filter_cons,List.filter_nil,
    show le (Dt n) (Z one)=true from Evidence.WF.le_of_lt (Dt_lt_Z1 n)]
  rfl

theorem phiShifted_Ct (n : Nat) : phiShifted zero (Ct n)=false := rfl
theorem splitFin_addZfD (n : Nat) :
    splitFin (add Z0t (fD n))=(add Z0t (fD n),0) :=
  Evidence.StageB.splitFin_add_pair (fD_isAP n) (fD_bne_one n)

theorem phiShifted_addZfD (n : Nat) : phiShifted zero (add Z0t (fD n))=false := by
  unfold phiShifted
  rw [splitFin_addZfD n]
  rfl

theorem logOm_Dt (n : Nat) : Trans.Dict.logOm (Dt n)=Ct n := rfl

theorem logOm_Ct (n : Nat) : Trans.Dict.logOm (Ct n)=add Z0t (fD n) := by
  show (if phiShifted zero (add Z0t (fD n)) then plus (add Z0t (fD n)) one
        else add Z0t (fD n))=_
  rw [phiShifted_addZfD n]
  rfl

theorem subAP_Z0t_addZfD (n : Nat) : Trans.Dict.subAP Z0t (add Z0t (fD n))=fD n := by
  unfold Trans.Dict.subAP
  rw [toList_addZfD n]
  show (if (Z0t==Z0t)=true then TM.Term.ofList [fD n] else add Z0t (fD n))=fD n
  rw [if_pos (show (Z0t==Z0t)=true from rfl)]
  rfl

theorem omegaNF_fD : ∀ n : Nat, omegaNF (fD n)=fD n
  | 0 => by decide
  | n+1 => by
    show omegaNF (phi (fD n) (plus Cps one))=_
    exact Rows.ProofsB.omegaNF_phi_ne_zero (by
      intro hc
      have : ((fD n)==zero)=true := beq_of_eq hc
      rw [fD_bne_zero n] at this
      exact Bool.noConfusion this)

theorem divAP_Ct (n : Nat) : Trans.Dict.divAP Z0t (Ct n)=fD n := by
  unfold Trans.Dict.divAP
  rw [logOm_Ct n,subAP_Z0t_addZfD n,omegaNF_fD n]

theorem wcnf_Dt (n : Nat) : Trans.Dict.wcnf Z0t [Dt n]=([(fD n,one)],zero) := by
  unfold Trans.Dict.wcnf
  rw [lt_Dt_Z0t n]
  simp only [Bool.false_eq_true,if_false,logOm_Dt,Ct_toList]
  simp only [List.filter_cons,List.filter_nil,lt_Ct_Z0t n,
    Bool.not_false,Bool.false_eq_true,if_true,if_false,
    List.map_cons,List.map_nil,divAP_Ct n,TM.Term.ofList,Trans.Dict.wcnf]
  rfl

theorem Z1_bne_fD (n : Nat) : ((Z one)==fD n)=false := by
  cases n <;> rfl

theorem wcnf_Z1_Dt (n : Nat) :
    Trans.Dict.wcnf Z0t [Z one,Dt n]=([(Z one,one),(fD n,one)],zero) := by
  rw [Trans.Dict.wcnf,if_neg (by decide)]
  simp only [Trans.Dict.logOm,TM.Term.toList,List.filter_cons,List.filter_nil,
    show lt (Z one) Z0t=false from by decide,
    Bool.not_false,Bool.false_eq_true,if_true,if_false,
    List.map_cons,List.map_nil,
    show Trans.Dict.divAP Z0t (Z one)=Z one from rfl,TM.Term.ofList]
  rw [wcnf_Dt n]
  simp only [Z1_bne_fD n,Bool.false_eq_true,if_false]
  rfl

theorem Cps_inT : inT Cps=true := by decide

theorem Cps_lt_fD : ∀ n : Nat, lt Cps (fD n)=true
  | 0 => by decide
  | n+1 => by
    show lt Cps (phi (fD n) (plus Cps one))=true
    unfold lt
    cases h:fuelOf Cps (phi (fD n) (plus Cps one)) with
    | zero => simp [fuelOf] at h
    | succ f =>
      have hf : Cps.deg+(fD n).deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      have key : TM.Term.ltF f Cps (fD n)=true := by
        rw [← Evidence.WF.lt_eq_ltF Cps (fD n) f hf]
        exact Cps_lt_fD n
      show (((Cps==fD n) || (Cps==plus Cps one)
        || TM.Term.ltF f Cps (fD n) || TM.Term.ltF f Cps (plus Cps one))=true)
      rw [key]
      simp only [Bool.or_true,Bool.true_or]

theorem lt_fD_Cps (n : Nat) : lt (fD n) Cps=false :=
  Evidence.WF.lt_asymm_inT Cps_inT (fD_inT n) (Cps_lt_fD n)

theorem le_Z0t_fD (n : Nat) : le Z0t (fD n)=false := by
  unfold le
  rw [show (Z0t==fD n)=false from beq_eq_false_iff_ne.mpr
    (Ne.symm (Evidence.WF.ne_of_ltF (fD_lt_Z0t n)))]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (fD_inT n) (by decide) (fD_lt_Z0t n)

theorem phiNF_fD (n : Nat) : phiNF (fD n) (plus Cps one)=fD (n+1) := by
  show phiNF (fD n) (add Cps one)=phi (fD n) (add Cps one)
  unfold phiNF
  simp only [TM.Term.isSC,Bool.false_and,Bool.false_eq_true,if_false]
  show phiNFsucc (fD n) (add Cps one)=phi (fD n) (add Cps one)
  unfold phiNFsucc
  rw [show splitFin (add Cps one)=(Cps,1) from rfl]
  simp only [ge_iff_le,Nat.le_refl,if_true]
  show (if (Cps.isSC && lt (fD n) Cps)=true then phi (fD n) (plus Cps (ofNat 0))
        else phiNFdefault (fD n) (add Cps one))=_
  rw [lt_fD_Cps n]
  simp only [Bool.and_false,Bool.false_eq_true,if_false]
  exact Rows.ProofsB.phiNFdefault_phi (by
    cases n <;> rfl)

/-- リンク 3 の一段。強臨界の枝で `ψ_Ω(Z1) = Cps` が出て、Veblen の枝がそれを底に使う。 -/
theorem collapse_zero_Dt (n : Nat) :
    Trans.Dict.collapse 0 (add (Z one) (Dt n))=fD (n+1) := by
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show (add (Z one) (Dt n)).toList=[Z one,Dt n] from rfl,wcnf_Z1_Dt n]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show le Z0t (Z one)=true from by decide]
  simp only [if_true]
  rw [le_Z0t_fD n]
  simp only [Bool.false_eq_true,if_false,Option.getD_some]
  rw [show Trans.Dict.sub1
      (Trans.Dict.mulL (Trans.Dict.mulL Z0t (Trans.Dict.subAP Z0t (Z one))) one)
      =Z one from rfl]
  rw [show psi Z0t (Z one)=Cps from rfl]
  rw [phiNF_fD n,show plus (fD (n+1)) zero=fD (n+1) from rfl,
    Rows.ProofsB.plus_zero_left (fD_isAP (n+1)),omegaNF_fD (n+1)]

theorem dict_D2z : Trans.Dict.dict D2z=Z one := rfl

theorem dict_D0_Base : Trans.Dict.dict (.D 0 Base)=fD 0 := rfl

theorem dict_D0_W : ∀ n : Nat, Trans.Dict.dict (.D 0 (W n Base))=fD n
  | 0 => dict_D0_Base
  | n+1 => by
    rw [W,Trans.Dict.dict_D,Trans.Dict.dict_sum,dict_D2z,
      Trans.Dict.dict_D,Trans.Dict.dict_D,dict_D0_W n,
      collapse_one_fD n,collapse_one_Ct n,plus_Z1_Dt n,collapse_zero_Dt n]

theorem LBT_phase0 (a : Nat) : LBT (5*a)=.D 0 (W a (Part 0)) := by
  unfold LBT
  rw [show 5*a/5=a by omega,show 5*a%5=0 by omega]

/-- Link 3: every complete five-column block advances the closed sequence `fD`. -/
theorem dict_LBT (n : Nat) : Trans.Dict.dict (LBT (5*n))=fD n := by
  rw [LBT_phase0]
  change Trans.Dict.dict (.D 0 (W n Base))=_
  rw [dict_D0_W]

#print axioms collapse_zero_Dt
#print axioms dict_LBT

#guard (List.range 5).all fun n => Trans.Dict.wcnf Z0t [Dt n]==([(fD n,one)],zero)
#guard (List.range 5).all fun n =>
  Trans.Dict.wcnf Z0t [Z one,Dt n]==([(Z one,one),(fD n,one)],zero)
#guard (List.range 5).all fun n =>
  Trans.Dict.collapse 0 (add (Z one) (Dt n))==fD (n+1)
#guard (List.range 5).all fun n => plus (Z one) (Dt n)==add (Z one) (Dt n)

-- 測定: 値は Veblen 断片ではない (ψ/Z を含む) が 𝔗(M) の項ではある
#guard !(Evidence.WF.CNV (fD 0))
#guard (List.range 6).all fun n => inT (fD n)
#guard (List.range 6).all fun n => lt (fD n) Z0t
#guard lt (plus Cps one) Z0t

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (5*n))
#guard (List.range 20).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard (List.range 20).all fun m => Trans.Recal.transPort (L m)==LBT m
#guard (List.range 20).all fun m => Trans.Recal.redP (L m)==L m
#guard rest12.any fun r => r.m==M && r.t==t
#guard (List.range 6).all fun n => Trans.oR (BMS.expand M n)==some (fD n)

#print axioms ofMatrix_M

end G12
end Rows.Selected
