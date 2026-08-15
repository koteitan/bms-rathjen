import Rows.G10
import Rows.Ladder

/-!
# G12 — Γ_{ψ₀(Ω₂)+1} の行 `(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`

`oR` が要る 12 行の最後の 1 行。展開の値の列は標準基本列ではなく閉じた形 `fD`
(`Rows/Selected.lean`) で、`Certified` の極限節はそれで構わない。

**3 つのリンクが全部定理になった。** `oR_M` が行を閉じる:

    oR (expand M n) = some (fD n)          全 n について

    展開 --ofMatrix--> 梯子 --transPort--> BT --dict--> 値
            ✅ ofMatrix_M    ✅ transPort_L   ✅ dict_LBT

還元の中身は **6 つの形の輪** で、`Aw E n` から出発して 6 歩で `Aw (E+3) (n-5)` に戻る。
輪が長さを 5 減らし、ずらしを 3 増やす。答え `RA n` はずらしに依らない — これが
`red_Aw_all` で、そこから `redP_L` と `isReducedP_L` が出る。

読み手は 5 相を回る。各 `L k` に付く印はただ 1 つで、位置は相で決まる
(`markJ`: 末尾、末尾、1 つ内、2 つ内、末尾)。相 2・3 だけが印を内側に置き、
そこだけ `Mark` が `replMark` を通る。

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

/-! ### Link 2, step 15: the window's own minimum, and its parent chain.

Everything the recursion touches is `h :: Win i d n` for a head `h` strictly below the
window.  Two facts about `Gp` carry the whole analysis: where the sequence attains its
minimum from an offset on, and that the row-zero parent is `parN`. -/

/-- The five residues, spelled out. -/
theorem Gp_r (a : Nat) :
    Gp (5*a+0)=((3*a:Nat):Int) ∧ Gp (5*a+1)=((3*a:Nat):Int)+1
    ∧ Gp (5*a+2)=((3*a:Nat):Int)+2 ∧ Gp (5*a+3)=((3*a:Nat):Int)+1
    ∧ Gp (5*a+4)=((3*a:Nat):Int)+2 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [Gp_val a 0 (by omega),if_pos rfl,Int.add_zero]
  · rw [Gp_val a 1 (by omega),if_neg (by omega),if_pos (Or.inl rfl)]
  · rw [Gp_val a 2 (by omega),if_neg (by omega),if_neg (by omega)]
  · rw [Gp_val a 3 (by omega),if_neg (by omega),if_pos (Or.inr rfl)]
  · rw [Gp_val a 4 (by omega),if_neg (by omega),if_neg (by omega)]

/-- `Gp` never drops below its value at an offset ≢ 2 (mod 5). -/
theorem Gp_min_le (i t : Nat) (hi : i%5 ≠ 2) (h : i ≤ t) : Gp i ≤ Gp t := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<5 ∧ i=5*a+r := ⟨i/5,i%5,by omega,by omega⟩
  obtain ⟨b,s,hs,rfl⟩ : ∃ b s, s<5 ∧ t=5*b+s := ⟨t/5,t%5,by omega,by omega⟩
  rw [show (5*a+r)%5=r by omega] at hi
  have hab : a ≤ b := by omega
  obtain ⟨e0,e1,e2,e3,e4⟩ := Gp_r a
  obtain ⟨f0,f1,f2,f3,f4⟩ := Gp_r b
  rcases (show r=0 ∨ r=1 ∨ r=3 ∨ r=4 by omega) with rfl|rfl|rfl|rfl <;>
    rcases (show s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 by omega) with rfl|rfl|rfl|rfl|rfl <;>
    simp only [e0,e1,e2,e3,e4,f0,f1,f2,f3,f4] <;> push_cast <;> omega

/-- Strictly, from an offset ≡ 0, 3, 4 (mod 5). -/
theorem Gp_min_lt (i t : Nat) (hi1 : i%5 ≠ 1) (hi2 : i%5 ≠ 2) (h : i<t) : Gp i<Gp t := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<5 ∧ i=5*a+r := ⟨i/5,i%5,by omega,by omega⟩
  obtain ⟨b,s,hs,rfl⟩ : ∃ b s, s<5 ∧ t=5*b+s := ⟨t/5,t%5,by omega,by omega⟩
  rw [show (5*a+r)%5=r by omega] at hi1 hi2
  have hab : a ≤ b := by omega
  obtain ⟨e0,e1,e2,e3,e4⟩ := Gp_r a
  obtain ⟨f0,f1,f2,f3,f4⟩ := Gp_r b
  rcases (show r=0 ∨ r=3 ∨ r=4 by omega) with rfl|rfl|rfl <;>
    rcases (show s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 by omega) with rfl|rfl|rfl|rfl|rfl <;>
    simp only [e0,e1,e2,e3,e4,f0,f1,f2,f3,f4] <;> push_cast <;> omega

/-- The row-zero parent drops the value. -/
theorem Gp_parN_lt (t : Nat) (ht : 1 ≤ t) : Gp (parN t)<Gp t := by
  unfold parN
  by_cases h3 : t%5=3
  · rw [if_pos h3]
    exact (Gp_three t h3).1
  · rw [if_neg h3]
    exact Gp_lt_step t ht h3

/-- …and nothing between the parent and the node drops it. -/
theorem Gp_parN_keep (t j : Nat) (h1 : parN t<j) (h2 : j<t) : Gp t ≤ Gp j := by
  unfold parN at h1
  by_cases h3 : t%5=3
  · rw [if_pos h3] at h1
    obtain ⟨_,hle2,hle1⟩ := Gp_three t h3
    rcases (show j=t-2 ∨ j=t-1 by omega) with rfl|rfl
    · exact hle2
    · exact hle1
  · rw [if_neg h3] at h1
    omega

theorem getD_Win (i : Nat) (d : Int) (n k : Nat) (hk : k<n) :
    (Win i d n).getD k (0,0)=(Gp (k+i)+d,Gq (k+i)) := by
  unfold Win
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

#guard (List.range 20).all fun i => (List.range 20).all fun t =>
  !(decide (i%5 ≠ 2 ∧ i ≤ t)) || decide (Gp i ≤ Gp t)
#guard (List.range 20).all fun i => (List.range 20).all fun t =>
  !(decide (i%5 ≠ 1 ∧ i%5 ≠ 2 ∧ i<t)) || decide (Gp i<Gp t)

/-! ### Link 2, step 16: one exceptional head over a window.

`Y`, `Zr` and the branch itself are all `h :: Win i d n` with `h`'s row-zero value
strictly below every column of the window.  That single hypothesis gives the parent
chain, hence `isPrincipalP` and `ppair`, for all of them at once. -/

/-- 例外的な頭 1 つの上に窓。 -/
def Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS := h :: Win i d n

theorem length_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    (Hd h i d n).length=n+1 := by
  unfold Hd
  rw [List.length_cons,length_Win]

theorem gp0_Hd (h : Int × Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+1) :
    Trans.Recal.gp0 (Hd h i d n) ((k:Nat):Int)
      = if k=0 then h.1 else Gp (k-1+i)+d := by
  show (if (((k:Nat):Int)<0) then 0 else ((Hd h i d n).getD k (0,0)).1)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Win i d n).getD j (0,0)).1=Gp (j+1-1+i)+d
    rw [getD_Win i d n j (by omega),show j+1-1=j from rfl]

theorem gp1_Hd (h : Int × Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+1) :
    Trans.Recal.gp1 (Hd h i d n) ((k:Nat):Int)
      = if k=0 then h.2 else Gq (k-1+i) := by
  show (if (((k:Nat):Int)<0) then 0 else ((Hd h i d n).getD k (0,0)).2)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Win i d n).getD j (0,0)).2=Gq (j+1-1+i)
    rw [getD_Win i d n j (by omega),show j+1-1=j from rfl]

/-- The row-zero value, as a function of the index. -/
def GH (c : Int) (i : Nat) (d : Int) (k : Nat) : Int :=
  if k=0 then c else Gp (k-1+i)+d

/-- The row-zero parent: the window's own parent when it stays inside, else the head. -/
def parHd (i k : Nat) : Nat := if i ≤ parN (k-1+i) then parN (k-1+i)-i+1 else 0

theorem parHd_lt (i k : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k) : parHd i k<k := by
  unfold parHd
  by_cases hc : i ≤ parN (k-1+i)
  · rw [if_pos hc]
    have := parN_lt (k-1+i) (by omega)
    omega
  · rw [if_neg hc]
    omega

theorem GH_drop (c : Int) (i : Nat) (d : Int) (n k : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k)
    (hkn : k<n+1) (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    GH c i d (parHd i k)<GH c i d k := by
  have ht : 1 ≤ k-1+i := by omega
  unfold parHd
  by_cases hc : i ≤ parN (k-1+i)
  · rw [if_pos hc]
    have he : parN (k-1+i)-i+1-1+i=parN (k-1+i) := by omega
    unfold GH
    rw [if_neg (by omega),if_neg (by omega),he]
    have := Gp_parN_lt (k-1+i) ht
    omega
  · rw [if_neg hc]
    unfold GH
    rw [if_pos rfl,if_neg (by omega)]
    exact hh (k-1+i) (by omega) (by omega)

theorem GH_keep (c : Int) (i : Nat) (d : Int) (k j : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k)
    (h1 : parHd i k<j) (h2 : j<k) : GH c i d k ≤ GH c i d j := by
  have hj : 1 ≤ j := by omega
  have hpar : parN (k-1+i)<j-1+i := by
    unfold parHd at h1
    by_cases hc : i ≤ parN (k-1+i)
    · rw [if_pos hc] at h1; omega
    · rw [if_neg hc] at h1; omega
  unfold GH
  rw [if_neg (by omega),if_neg (by omega)]
  have := Gp_parN_keep (k-1+i) (j-1+i) hpar (by omega)
  omega

theorem chain_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i)
    (hh : ∀ t, i ≤ t → t<i+n → h.1<Gp t+d) :
    ∀ k, 1 ≤ k → k<(Hd h i d n).length →
      Trans.Recal.fpar (Hd h i d n) 0 ((k:Nat):Int) 0=((parHd i k : Nat) : Int) :=
  Rows.Ladder.fpar_of_gap
    (G := GH h.1 i d) (par := parHd i)
    (fun k hk => by
      rw [length_Hd] at hk
      rw [gp0_Hd h i d n k hk]
      rfl)
    (fun k hk1 _ => parHd_lt i k hi hk1)
    (fun k hk1 hk => by
      rw [length_Hd] at hk
      exact GH_drop h.1 i d n k hi hk1 hk hh)
    (fun k j hk1 _ h1 h2 => GH_keep h.1 i d k j hi hk1 h1 h2)

theorem root_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.fpar (Hd h i d n) 0 ((0:Nat):Int) 0=-1 :=
  Rows.Ladder.fpar_zero_of_gap
    (G := GH h.1 i d)
    (fun k hk => by
      rw [length_Hd] at hk
      rw [gp0_Hd h i d n k hk]
      rfl)
    (by rw [length_Hd]; omega)

theorem isPrincipalP_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i)
    (hn : 1 ≤ n) (hh : ∀ t, i ≤ t → t<i+n → h.1<Gp t+d) :
    Trans.Recal.isPrincipalP (Hd h i d n)=true :=
  Rows.Ladder.isPrincipalP_of_chain (chain_Hd h i d n hi hh)
    (fun k hk1 _ => parHd_lt i k hi hk1) (root_Hd h i d n)
    (by rw [length_Hd]; omega)

theorem ppair_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i)
    (hh : ∀ t, i ≤ t → t<i+n → h.1<Gp t+d) :
    Trans.Recal.ppair (Hd h i d n)=[Hd h i d n] :=
  Rows.Ladder.ppair_of_chain (chain_Hd h i d n hi hh)
    (fun k hk1 _ => parHd_lt i k hi hk1) (root_Hd h i d n)
    (by rw [length_Hd]; omega)

/-- 窓そのものも、先頭を頭と見れば `Hd`。`i%5 ∈ {0,3,4}` のとき先頭は最小。 -/
theorem Win_eq_Hd (i : Nat) (d : Int) (n : Nat) :
    Win i d (n+1)=Hd (Gp i+d,Gq i) (i+1) d n := by
  unfold Hd
  rw [Win_cons]

theorem ppair_Win (i : Nat) (d : Int) (n : Nat) (hi1 : i%5 ≠ 1) (hi2 : i%5 ≠ 2) :
    Trans.Recal.ppair (Win i d (n+1))=[Win i d (n+1)] := by
  rw [Win_eq_Hd]
  exact ppair_Hd _ (i+1) d n (by omega)
    (fun t ht _ => by
      have := Gp_min_lt i t hi1 hi2 (by omega)
      show Gp i+d<Gp t+d
      omega)

theorem isPrincipalP_Win (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n)
    (hi1 : i%5 ≠ 1) (hi2 : i%5 ≠ 2) :
    Trans.Recal.isPrincipalP (Win i d (n+1))=true := by
  rw [Win_eq_Hd]
  exact isPrincipalP_Hd _ (i+1) d n (by omega) hn
    (fun t ht _ => by
      have := Gp_min_lt i t hi1 hi2 (by omega)
      show Gp i+d<Gp t+d
      omega)

#guard (List.range 6).all fun i => (List.range 8).all fun n =>
  !(decide (i%5 ≠ 1 ∧ i%5 ≠ 2)) ||
    (Trans.Recal.ppair (Win i 1 (n+1))==[Win i 1 (n+1)])

/-! ### Link 2, step 17: two exceptional heads over a window.

The folded ladders carry a `(0,0)` above `Hd`'s head.  The parent chain just shifts. -/

/-- 頭 `(0,0)` と `(c,1)` の上に窓。畳み込みに入る形。 -/
def A2 (c : Int) (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS :=
  ((0:Int),(0:Int)) :: Hd (c,1) i d n

theorem length_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    (A2 c i d n).length=n+2 := by
  unfold A2
  rw [List.length_cons,length_Hd]

theorem gp0_A2 (c : Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+2) :
    Trans.Recal.gp0 (A2 c i d n) ((k:Nat):Int)
      = if k=0 then 0 else if k=1 then c else Gp (k-2+i)+d := by
  show (if (((k:Nat):Int)<0) then 0 else ((A2 c i d n).getD k (0,0)).1)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Hd (c,1) i d n).getD j (0,0)).1=_
    have h := gp0_Hd (c,1) i d n j (by omega)
    rw [show Trans.Recal.gp0 (Hd (c,1) i d n) ((j:Nat):Int)
        = (if (((j:Nat):Int)<0) then 0 else ((Hd (c,1) i d n).getD j (0,0)).1) from rfl,
      if_neg (by omega)] at h
    rw [h,show j+1-2=j-1 from rfl]
    cases j with
    | zero => rw [if_pos rfl,if_pos rfl]
    | succ jj => rw [if_neg (by omega),if_neg (by omega)]

theorem gp1_A2 (c : Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+2) :
    Trans.Recal.gp1 (A2 c i d n) ((k:Nat):Int)
      = if k=0 then 0 else if k=1 then 1 else Gq (k-2+i) := by
  show (if (((k:Nat):Int)<0) then 0 else ((A2 c i d n).getD k (0,0)).2)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Hd (c,1) i d n).getD j (0,0)).2=_
    have h := gp1_Hd (c,1) i d n j (by omega)
    rw [show Trans.Recal.gp1 (Hd (c,1) i d n) ((j:Nat):Int)
        = (if (((j:Nat):Int)<0) then 0 else ((Hd (c,1) i d n).getD j (0,0)).2) from rfl,
      if_neg (by omega)] at h
    rw [h,show j+1-2=j-1 from rfl]
    cases j with
    | zero => rw [if_pos rfl,if_pos rfl]
    | succ jj => rw [if_neg (by omega),if_neg (by omega)]

def GA (c : Int) (i : Nat) (d : Int) (k : Nat) : Int :=
  if k=0 then 0 else if k=1 then c else Gp (k-2+i)+d

theorem GA_succ (c : Int) (i : Nat) (d : Int) (j : Nat) : GA c i d (j+1)=GH c i d j := by
  unfold GA GH
  cases j with
  | zero => rfl
  | succ jj => rfl

def parA (i k : Nat) : Nat := if k ≤ 1 then 0 else parHd i (k-1)+1

theorem parA_lt (i k : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k) : parA i k<k := by
  unfold parA
  by_cases h1 : k ≤ 1
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    have := parHd_lt i (k-1) hi (by omega)
    omega

theorem GA_drop (c : Int) (i : Nat) (d : Int) (n k : Nat) (hi : 1 ≤ i) (hc : 0<c)
    (hk : 1 ≤ k) (hkn : k<n+2) (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    GA c i d (parA i k)<GA c i d k := by
  unfold parA
  by_cases h1 : k ≤ 1
  · rw [if_pos h1]
    have hk1 : k=1 := by omega
    subst hk1
    show GA c i d 0<GA c i d 1
    unfold GA
    rw [if_pos rfl]
    rw [show (if (1:Nat)=0 then (0:Int) else if (1:Nat)=1 then c else Gp (1-2+i)+d)=c
      from rfl]
    exact hc
  · rw [if_neg h1]
    obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
    rw [show j+1-1=j from rfl,GA_succ,GA_succ]
    exact GH_drop c i d n j hi (by omega) (by omega) hh

theorem GA_keep (c : Int) (i : Nat) (d : Int) (k j : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k)
    (h1 : parA i k<j) (h2 : j<k) : GA c i d k ≤ GA c i d j := by
  unfold parA at h1
  by_cases hone : k ≤ 1
  · rw [if_pos hone] at h1; omega
  · rw [if_neg hone] at h1
    obtain ⟨k1,rfl⟩ : ∃ k1, k=k1+1 := ⟨k-1,by omega⟩
    obtain ⟨j1,rfl⟩ : ∃ j1, j=j1+1 := ⟨j-1,by omega⟩
    rw [GA_succ,GA_succ]
    rw [show k1+1-1=k1 from rfl] at h1
    exact GH_keep c i d k1 j1 hi (by omega) (by omega) (by omega)

theorem chain_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i) (hc : 0<c)
    (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    ∀ k, 1 ≤ k → k<(A2 c i d n).length →
      Trans.Recal.fpar (A2 c i d n) 0 ((k:Nat):Int) 0=((parA i k : Nat) : Int) :=
  Rows.Ladder.fpar_of_gap
    (G := GA c i d) (par := parA i)
    (fun k hk => by
      rw [length_A2] at hk
      rw [gp0_A2 c i d n k hk]
      rfl)
    (fun k hk1 _ => parA_lt i k hi hk1)
    (fun k hk1 hk => by
      rw [length_A2] at hk
      exact GA_drop c i d n k hi hc hk1 hk hh)
    (fun k j hk1 _ h1 h2 => GA_keep c i d k j hi hk1 h1 h2)

theorem root_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.fpar (A2 c i d n) 0 ((0:Nat):Int) 0=-1 :=
  Rows.Ladder.fpar_zero_of_gap
    (G := GA c i d)
    (fun k hk => by
      rw [length_A2] at hk
      rw [gp0_A2 c i d n k hk]
      rfl)
    (by rw [length_A2]; omega)

theorem isPrincipalP_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i) (hc : 0<c)
    (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    Trans.Recal.isPrincipalP (A2 c i d n)=true :=
  Rows.Ladder.isPrincipalP_of_chain (chain_A2 c i d n hi hc hh)
    (fun k hk1 _ => parA_lt i k hi hk1) (root_A2 c i d n)
    (by rw [length_A2]; omega)

/-! ### Link 2, step 18: the six shapes of the cycle.

The recursion visits exactly six ladders, and they all live at window offsets 4, 5, 6:

    Q1 e s = (1,1) :: Win 4 e s              V m = Q1 0 (m+1)
    Aw E n = (0,0) :: (2,1) :: Win 4 E n
    Q2 E k = (2,1) :: Win 5 E k
    Bw D k = (0,0) :: (3,1) :: Win 5 D k
    Zw D t = (2,0) :: Win 6 D t
    Cw G t = (0,0) :: Win 6 G t

`Q1 → Aw → Q2 → Bw → Zw → Cw → Q1` drops the length by five and raises the shift by
three, and the shift never reaches the answer. -/

def Q1 (e : Int) (s : Nat) : Trans.Recal.PS := Hd ((1:Int),(1:Int)) 4 e s
def Aw (E : Int) (n : Nat) : Trans.Recal.PS := A2 2 4 E n
def Q2 (E : Int) (k : Nat) : Trans.Recal.PS := Hd ((2:Int),(1:Int)) 5 E k
def Bw (D : Int) (k : Nat) : Trans.Recal.PS := A2 3 5 D k
def Zw (D : Int) (t : Nat) : Trans.Recal.PS := Hd ((2:Int),(0:Int)) 6 D t
def Cw (G : Int) (t : Nat) : Trans.Recal.PS := Hd ((0:Int),(0:Int)) 6 G t

/-- `Aw` の答え。 -/
def RA (n : Nat) : Trans.Recal.PS :=
  ((0:Int),(0:Int)) :: ((1:Int),(1:Int)) :: Win 4 0 n
/-- `Q2` の答え。 -/
def RQ (k : Nat) : Trans.Recal.PS := ((1:Int),(1:Int)) :: Win 5 (-1) k

theorem Y_eq_Hd (c : Int) (i : Nat) (d : Int) (n : Nat) : Y c i d n=Hd (c,1) i d n := rfl
theorem Zr_eq_Hd (c : Int) (i : Nat) (d : Int) (n : Nat) : Zr c i d n=Hd (c,0) i d n := rfl
theorem A2_cons (c : Int) (i : Nat) (d : Int) (n : Nat) :
    A2 c i d n=((0:Int),(0:Int)) :: Y c i d n := rfl

theorem Gp_4 : Gp 4=2 := by decide
theorem Gp_5 : Gp 5=3 := by decide
theorem Gp_6 : Gp 6=4 := by decide
theorem Gp_7 : Gp 7=5 := by decide
theorem Gp_8 : Gp 8=4 := by decide
theorem Gq_3 : Gq 3=1 := by decide
theorem Gq_4 : Gq 4=1 := by decide
theorem Gq_5 : Gq 5=0 := by decide
theorem Gq_6 : Gq 6=1 := by decide
theorem Gq_7 : Gq 7=2 := by decide
theorem Gq_8 : Gq 8=1 := by decide

theorem Gp_ge_four (t : Nat) (ht : 4 ≤ t) : (2:Int) ≤ Gp t := by
  have := Gp_min_le 4 t (by omega) ht
  rw [Gp_4] at this
  omega

theorem Gp_ge_five (t : Nat) (ht : 5 ≤ t) : (3:Int) ≤ Gp t := by
  have := Gp_min_le 5 t (by omega) ht
  rw [Gp_5] at this
  omega

theorem Gp_ge_six (t : Nat) (ht : 6 ≤ t) : (4:Int) ≤ Gp t := by
  have := Gp_min_le 6 t (by omega) ht
  rw [Gp_6] at this
  omega

/-! #### 頭が窓より小さいこと -/

theorem head_Q1 (e : Int) (s : Nat) (he : 0 ≤ e) :
    ∀ t, 4 ≤ t → t<4+s → ((1:Int),(1:Int)).1<Gp t+e := by
  intro t ht _
  have := Gp_ge_four t ht
  show (1:Int)<Gp t+e
  omega

theorem head_Aw (E : Int) (n : Nat) (hE : 1 ≤ E) :
    ∀ t, 4 ≤ t → t<4+n → (2:Int)<Gp t+E := by
  intro t ht _
  have := Gp_ge_four t ht
  omega

theorem head_Q2 (E : Int) (k : Nat) (hE : 0 ≤ E) :
    ∀ t, 5 ≤ t → t<5+k → ((2:Int),(1:Int)).1<Gp t+E := by
  intro t ht _
  have := Gp_ge_five t ht
  show (2:Int)<Gp t+E
  omega

theorem head_Bw (D : Int) (k : Nat) (hD : 1 ≤ D) :
    ∀ t, 5 ≤ t → t<5+k → (3:Int)<Gp t+D := by
  intro t ht _
  have := Gp_ge_five t ht
  omega

theorem head_Zw (D : Int) (t0 : Nat) (hD : (-1:Int) ≤ D) :
    ∀ t, 6 ≤ t → t<6+t0 → ((2:Int),(0:Int)).1<Gp t+D := by
  intro t ht _
  have := Gp_ge_six t ht
  show (2:Int)<Gp t+D
  omega

theorem head_Cw (G : Int) (t0 : Nat) (hG : (-3:Int) ≤ G) :
    ∀ t, 6 ≤ t → t<6+t0 → ((0:Int),(0:Int)).1<Gp t+G := by
  intro t ht _
  have := Gp_ge_six t ht
  show (0:Int)<Gp t+G
  omega

theorem head_RQ (k : Nat) :
    ∀ t, 5 ≤ t → t<5+k → ((1:Int),(1:Int)).1<Gp t+(-1) := by
  intro t ht _
  have := Gp_ge_five t ht
  show (1:Int)<Gp t+(-1)
  omega

/-! #### 主要性 -/

theorem prin_Hd_any (c b : Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i)
    (hb : (b==0)=false) (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    Trans.Recal.isPrincipalP (Hd (c,b) i d n)=true := by
  cases n with
  | zero => exact Rows.Ladder.isPrincipalP_single c b hb
  | succ nn => exact isPrincipalP_Hd (c,b) i d (nn+1) hi (by omega) hh

theorem prin_Q1 (e : Int) (s : Nat) (he : 0 ≤ e) :
    Trans.Recal.isPrincipalP (Q1 e s)=true :=
  prin_Hd_any 1 1 4 e s (by omega) (by decide) (head_Q1 e s he)

theorem prin_Q2 (E : Int) (k : Nat) (hE : 0 ≤ E) :
    Trans.Recal.isPrincipalP (Q2 E k)=true :=
  prin_Hd_any 2 1 5 E k (by omega) (by decide) (head_Q2 E k hE)

theorem prin_RQ (k : Nat) : Trans.Recal.isPrincipalP (RQ k)=true :=
  prin_Hd_any 1 1 5 (-1) k (by omega) (by decide) (head_RQ k)

theorem prin_Zw (D : Int) (t : Nat) (hD : (-1:Int) ≤ D) (ht : 1 ≤ t) :
    Trans.Recal.isPrincipalP (Zw D t)=true :=
  isPrincipalP_Hd (2,0) 6 D t (by omega) ht (head_Zw D t hD)

theorem prin_Cw (G : Int) (t : Nat) (hG : (-3:Int) ≤ G) (ht : 1 ≤ t) :
    Trans.Recal.isPrincipalP (Cw G t)=true :=
  isPrincipalP_Hd (0,0) 6 G t (by omega) ht (head_Cw G t hG)

theorem prin_Aw (E : Int) (n : Nat) (hE : 1 ≤ E) :
    Trans.Recal.isPrincipalP (Aw E n)=true :=
  isPrincipalP_A2 2 4 E n (by omega) (by omega) (head_Aw E n hE)

theorem prin_Bw (D : Int) (k : Nat) (hD : 1 ≤ D) :
    Trans.Recal.isPrincipalP (Bw D k)=true :=
  isPrincipalP_A2 3 5 D k (by omega) (by omega) (head_Bw D k hD)

theorem prin_Win_three (s : Nat) : Trans.Recal.isPrincipalP (Win 3 0 (s+1))=true := by
  rw [Win_eq_Hd]
  exact prin_Hd_any (Gp 3+0) (Gq 3) 4 0 s (by omega) (by decide)
    (fun t ht _ => by
      have := Gp_ge_four t ht
      show Gp 3+0<Gp t+0
      rw [show Gp 3=1 from by decide]
      omega)

#guard (List.range 8).all fun s => Trans.Recal.isPrincipalP (Win 3 0 (s+1))
#guard (List.range 8).all fun k => Trans.Recal.isPrincipalP (RQ k)

/-! ### Link 2, step 19: the small indices.

`trMax`, `joints` and `nJ` only ever look at columns 0–3. -/

theorem gp0_Hd_0 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (Hd h i d n) 0=h.1 := rfl
theorem gp1_Hd_0 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (Hd h i d n) 0=h.2 := rfl

theorem gp0_Hd_1 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp0 (Hd h i d n) 1=Gp i+d := by
  show (if ((1:Int)<0) then 0 else ((Hd h i d n).getD 1 (0,0)).1)=Gp i+d
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).1=Gp i+d
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp1_Hd_1 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp1 (Hd h i d n) 1=Gq i := by
  show (if ((1:Int)<0) then 0 else ((Hd h i d n).getD 1 (0,0)).2)=Gq i
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).2=Gq i
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp0_Hd_2 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 2 ≤ n) :
    Trans.Recal.gp0 (Hd h i d n) 2=Gp (1+i)+d := by
  show (if ((2:Int)<0) then 0 else ((Hd h i d n).getD 2 (0,0)).1)=Gp (1+i)+d
  rw [if_neg (by omega)]
  show ((Win i d n).getD 1 (0,0)).1=Gp (1+i)+d
  rw [getD_Win i d n 1 (by omega)]

theorem gp1_Hd_2 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 2 ≤ n) :
    Trans.Recal.gp1 (Hd h i d n) 2=Gq (1+i) := by
  show (if ((2:Int)<0) then 0 else ((Hd h i d n).getD 2 (0,0)).2)=Gq (1+i)
  rw [if_neg (by omega)]
  show ((Win i d n).getD 1 (0,0)).2=Gq (1+i)
  rw [getD_Win i d n 1 (by omega)]

theorem gp0_Hd_3 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 3 ≤ n) :
    Trans.Recal.gp0 (Hd h i d n) 3=Gp (2+i)+d := by
  show (if ((3:Int)<0) then 0 else ((Hd h i d n).getD 3 (0,0)).1)=Gp (2+i)+d
  rw [if_neg (by omega)]
  show ((Win i d n).getD 2 (0,0)).1=Gp (2+i)+d
  rw [getD_Win i d n 2 (by omega)]

theorem gp1_Hd_3 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 3 ≤ n) :
    Trans.Recal.gp1 (Hd h i d n) 3=Gq (2+i) := by
  show (if ((3:Int)<0) then 0 else ((Hd h i d n).getD 3 (0,0)).2)=Gq (2+i)
  rw [if_neg (by omega)]
  show ((Win i d n).getD 2 (0,0)).2=Gq (2+i)
  rw [getD_Win i d n 2 (by omega)]

theorem gp0_A2_0 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (A2 c i d n) 0=0 := rfl
theorem gp1_A2_0 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (A2 c i d n) 0=0 := rfl
theorem gp0_A2_1 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (A2 c i d n) 1=c := rfl
theorem gp1_A2_1 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (A2 c i d n) 1=1 := rfl

theorem gp0_A2_2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp0 (A2 c i d n) 2=Gp i+d := by
  show (if ((2:Int)<0) then 0 else ((A2 c i d n).getD 2 (0,0)).1)=Gp i+d
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).1=Gp i+d
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp1_A2_2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp1 (A2 c i d n) 2=Gq i := by
  show (if ((2:Int)<0) then 0 else ((A2 c i d n).getD 2 (0,0)).2)=Gq i
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).2=Gq i
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem lenI_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.lenI (Hd h i d n)=((n:Nat):Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_Hd]
  omega

theorem lenI_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.lenI (A2 c i d n)=((n:Nat):Int)+2 := by
  unfold Trans.Recal.lenI
  rw [length_A2]
  omega

/-! #### `trMax` -/

theorem trMax_A2_one (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) (hc : 0<c)
    (h2 : c<Gp i+d) (h3 : ¬((1:Int)<Gq i)) : Trans.Recal.trMax (A2 c i d n)=1 := by
  have hlen : (A2 c i d n).length=n+2 := length_A2 c i d n
  have e1 : Trans.Recal.trMax (A2 c i d n)=(((1:Nat)):Int) → Trans.Recal.trMax (A2 c i d n)=1 :=
    fun h => by rw [h]; rfl
  apply e1
  refine Rows.Ladder.trMax_eq _ 1 (by omega) ?_ ?_
  · intro j hj
    have hj0 : j=0 := by omega
    subst hj0
    refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
      (by rw [lenI_A2]; omega) ?_
    have : Trans.Recal.fpar (A2 c i d n) 1 1 0=0 :=
      Rows.Ladder.fpar1_one _ (by omega)
        (by rw [gp0_A2_0,gp0_A2_1]; exact hc)
        (by rw [gp1_A2_0,gp1_A2_1]; omega)
    simpa using this
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have : Trans.Recal.fpar (A2 c i d n) 1 2 1=-1 :=
      Rows.Ladder.fpar1_two_lb _ (by omega)
        (by rw [gp0_A2_1,gp0_A2_2 c i d n hn]; exact h2)
        (by rw [gp1_A2_1,gp1_A2_2 c i d n hn]; exact h3)
    simpa using this

theorem trMax_A2_zero (c : Int) (i : Nat) (d : Int) (hc : 0<c) :
    Trans.Recal.trMax (A2 c i d 0)=1 := by
  have e1 : Trans.Recal.trMax (A2 c i d 0)=(((1:Nat)):Int) →
      Trans.Recal.trMax (A2 c i d 0)=1 := fun h => by rw [h]; rfl
  apply e1
  refine Rows.Ladder.trMax_eq _ 1 (by rw [length_A2]; omega) ?_ ?_
  · intro j hj
    have hj0 : j=0 := by omega
    subst hj0
    refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
      (by rw [lenI_A2]; omega) ?_
    have : Trans.Recal.fpar (A2 c i d 0) 1 1 0=0 :=
      Rows.Ladder.fpar1_one _ (by rw [length_A2]; omega)
        (by rw [gp0_A2_0,gp0_A2_1]; exact hc)
        (by rw [gp1_A2_0,gp1_A2_1]; omega)
    simpa using this
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have : Trans.Recal.fpar (A2 c i d 0) 1 2 1=-1 :=
      Rows.Ladder.fpar_out _ 1 2 1 (by rw [lenI_A2]; omega)
    simpa using this

theorem trMax_Cw (G : Int) (t : Nat) (ht : 3 ≤ t) (hG : (-3:Int) ≤ G) :
    Trans.Recal.trMax (Cw G t)=2 := by
  have e1 : Trans.Recal.trMax (Cw G t)=(((2:Nat)):Int) → Trans.Recal.trMax (Cw G t)=2 :=
    fun h => by rw [h]; rfl
  apply e1
  unfold Cw
  refine Rows.Ladder.trMax_eq _ 2 (by rw [length_Hd]; omega) ?_ ?_
  · intro j hj
    rcases (show j=0 ∨ j=1 by omega) with rfl|rfl
    · refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
        (by rw [lenI_Hd]; omega) ?_
      have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G t) 1 1 0=0 :=
        Rows.Ladder.fpar1_one _ (by rw [length_Hd]; omega)
          (by rw [gp0_Hd_0,gp0_Hd_1 _ 6 G t (by omega),Gp_6]; omega)
          (by rw [gp1_Hd_0,gp1_Hd_1 _ 6 G t (by omega),Gq_6]; omega)
      simpa using this
    · refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
        (by rw [lenI_Hd]; omega) ?_
      have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G t) 1 2 1=1 :=
        Rows.Ladder.fpar1_two_lb_eq _ (by rw [length_Hd]; omega)
          (by rw [gp0_Hd_1 _ 6 G t (by omega),gp0_Hd_2 _ 6 G t (by omega),
            show (1+6)=7 from rfl,Gp_6,Gp_7]; omega)
          (by rw [gp1_Hd_1 _ 6 G t (by omega),gp1_Hd_2 _ 6 G t (by omega),
            show (1+6)=7 from rfl,Gq_6,Gq_7]; omega)
      simpa using this
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G t) 1 3 2=-1 :=
      Rows.Ladder.fpar1_three_lb _ (by rw [length_Hd]; omega)
        (by rw [gp0_Hd_2 _ 6 G t (by omega),gp0_Hd_3 _ 6 G t (by omega),
          show (1+6)=7 from rfl,show (2+6)=8 from rfl,Gp_7,Gp_8]; omega)
    simpa using this

theorem trMax_Cw_one (G : Int) (hG : (-3:Int) ≤ G) : Trans.Recal.trMax (Cw G 1)=1 := by
  have e1 : Trans.Recal.trMax (Cw G 1)=(((1:Nat)):Int) → Trans.Recal.trMax (Cw G 1)=1 :=
    fun h => by rw [h]; rfl
  apply e1
  unfold Cw
  refine Rows.Ladder.trMax_eq _ 1 (by rw [length_Hd]; omega) ?_ ?_
  · intro j hj
    have hj0 : j=0 := by omega
    subst hj0
    refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
      (by rw [lenI_Hd]; omega) ?_
    have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G 1) 1 1 0=0 :=
      Rows.Ladder.fpar1_one _ (by rw [length_Hd]; omega)
        (by rw [gp0_Hd_0,gp0_Hd_1 _ 6 G 1 (by omega),Gp_6]; omega)
        (by rw [gp1_Hd_0,gp1_Hd_1 _ 6 G 1 (by omega),Gq_6]; omega)
    simpa using this
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G 1) 1 2 1=-1 :=
      Rows.Ladder.fpar_out _ 1 2 1 (by rw [lenI_Hd]; omega)
    simpa using this

theorem trMax_Cw_two (G : Int) (hG : (-3:Int) ≤ G) : Trans.Recal.trMax (Cw G 2)=2 := by
  have e1 : Trans.Recal.trMax (Cw G 2)=(((2:Nat)):Int) → Trans.Recal.trMax (Cw G 2)=2 :=
    fun h => by rw [h]; rfl
  apply e1
  unfold Cw
  refine Rows.Ladder.trMax_eq _ 2 (by rw [length_Hd]; omega) ?_ ?_
  · intro j hj
    rcases (show j=0 ∨ j=1 by omega) with rfl|rfl
    · refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
        (by rw [lenI_Hd]; omega) ?_
      have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G 2) 1 1 0=0 :=
        Rows.Ladder.fpar1_one _ (by rw [length_Hd]; omega)
          (by rw [gp0_Hd_0,gp0_Hd_1 _ 6 G 2 (by omega),Gp_6]; omega)
          (by rw [gp1_Hd_0,gp1_Hd_1 _ 6 G 2 (by omega),Gq_6]; omega)
      simpa using this
    · refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
        (by rw [lenI_Hd]; omega) ?_
      have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G 2) 1 2 1=1 :=
        Rows.Ladder.fpar1_two_lb_eq _ (by rw [length_Hd]; omega)
          (by rw [gp0_Hd_1 _ 6 G 2 (by omega),gp0_Hd_2 _ 6 G 2 (by omega),
            show (1+6)=7 from rfl,Gp_6,Gp_7]; omega)
          (by rw [gp1_Hd_1 _ 6 G 2 (by omega),gp1_Hd_2 _ 6 G 2 (by omega),
            show (1+6)=7 from rfl,Gq_6,Gq_7]; omega)
      simpa using this
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have : Trans.Recal.fpar (Hd ((0:Int),(0:Int)) 6 G 2) 1 3 2=-1 :=
      Rows.Ladder.fpar_out _ 1 3 2 (by rw [lenI_Hd]; omega)
    simpa using this

#guard (List.range 6).all fun n => Trans.Recal.trMax (Aw 1 (n+1))==1
#guard (List.range 6).all fun k => Trans.Recal.trMax (Bw 2 (k+1))==1
#guard (List.range 6).all fun t => Trans.Recal.trMax (Cw 0 (t+3))==2
#guard Trans.Recal.trMax (Cw 0 1)==1
#guard Trans.Recal.trMax (Cw 0 2)==2

/-! ### Link 2, step 20: the branch, and the three folds. -/

theorem drop_A2_two (c : Int) (i : Nat) (d : Int) (n : Nat) :
    (A2 c i d n).drop 2=Win i d n := rfl

theorem drop_Hd_three (h : Int × Int) (i : Nat) (d : Int) (t : Nat) (ht : 2 ≤ t) :
    (Hd h i d t).drop 3=Win (i+2) d (t-2) := by
  show (Win i d t).drop 2=Win (i+2) d (t-2)
  obtain ⟨u,rfl⟩ : ∃ u, t=u+2 := ⟨t-2,by omega⟩
  rw [show (u+2)=(u+1)+1 from rfl,show ((Win i d ((u+1)+1)).drop 2)
      =(((Win i d ((u+1)+1)).drop 1).drop 1) from by
    rw [List.drop_drop]]
  rw [Win_drop i d (u+1),Win_drop (i+1) d u,show i+1+1=i+2 from rfl,
    show u+2-2=u from rfl]

theorem brF_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n)
    (htr : Trans.Recal.trMax (A2 c i d n)=1) (hi1 : i%5 ≠ 1) (hi2 : i%5 ≠ 2) :
    Trans.Recal.brF (A2 c i d n)=[Win i d n] := by
  unfold Trans.Recal.brF
  rw [htr,show ((1:Int)+1).toNat=2 from by rfl,drop_A2_two]
  obtain ⟨u,rfl⟩ : ∃ u, n=u+1 := ⟨n-1,by omega⟩
  exact ppair_Win i d u hi1 hi2

theorem brF_Cw (G : Int) (t : Nat) (ht : 3 ≤ t) (hG : (-3:Int) ≤ G) :
    Trans.Recal.brF (Cw G t)=[Win 8 G (t-2)] := by
  unfold Trans.Recal.brF
  rw [trMax_Cw G t ht hG,show ((2:Int)+1).toNat=3 from by rfl]
  unfold Cw
  rw [drop_Hd_three _ 6 G t (by omega),show (6+2)=8 from rfl]
  obtain ⟨u,hu⟩ : ∃ u, t-2=u+1 := ⟨t-3,by omega⟩
  rw [hu]
  exact ppair_Win 8 G u (by omega) (by omega)

theorem joint_Aw (E : Int) (n : Nat) (hE : 1 ≤ E) (hn : 1 ≤ n) :
    Trans.Recal.fpar (Aw E n) 0 2 0=1 := by
  have h := chain_A2 2 4 E n (by omega) (by omega) (head_Aw E n hE) 2 (by omega)
    (by rw [length_A2]; omega)
  rw [show parA 4 2=1 from by decide] at h
  simpa using h

theorem joint_Bw (D : Int) (k : Nat) (hD : 1 ≤ D) (hk : 1 ≤ k) :
    Trans.Recal.fpar (Bw D k) 0 2 0=1 := by
  have h := chain_A2 3 5 D k (by omega) (by omega) (head_Bw D k hD) 2 (by omega)
    (by rw [length_A2]; omega)
  rw [show parA 5 2=1 from by decide] at h
  simpa using h

theorem joint_Cw (G : Int) (t : Nat) (hG : (-3:Int) ≤ G) (ht : 3 ≤ t) :
    Trans.Recal.fpar (Cw G t) 0 3 0=0 := by
  have h := chain_Hd ((0:Int),(0:Int)) 6 G t (by omega) (head_Cw G t hG) 3 (by omega)
    (by rw [length_Hd]; omega)
  rw [show parHd 6 3=0 from by decide] at h
  simpa using h

theorem nJ_Aw (E : Int) (n : Nat) (hE : 1 ≤ E) (hn : 1 ≤ n) :
    Trans.Recal.fpar (Aw E n) 1 2 0=0 := by
  unfold Aw
  exact Rows.Ladder.fpar1_two_zero _ (by rw [length_A2]; omega)
    (joint_Aw E n hE hn)
    (by rw [gp0_A2_0,gp0_A2_1]; omega)
    (by rw [gp1_A2_1,gp1_A2_2 2 4 E n hn,Gq_4]; omega)
    (by rw [gp1_A2_0,gp1_A2_2 2 4 E n hn,Gq_4]; omega)

theorem nJ_Cw (G : Int) (t : Nat) (hG : (-3:Int) ≤ G) (ht : 3 ≤ t) :
    Trans.Recal.fpar (Cw G t) 1 3 0=0 := by
  unfold Cw
  exact Rows.Ladder.fpar1_three_zero _ (by rw [length_Hd]; omega)
    (joint_Cw G t hG ht)
    (by rw [gp1_Hd_0,gp1_Hd_3 _ 6 G t (by omega),show (2+6)=8 from rfl,Gq_8]; omega)

theorem isZeroP_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.isZeroP (A2 c i d n)=false := by
  unfold Trans.Recal.isZeroP
  rw [show ((A2 c i d n).length==1)=false from by rw [length_A2]; simp]
  rfl

theorem isZeroP_Hd_of_len (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.isZeroP (Hd h i d n)=false := by
  unfold Trans.Recal.isZeroP
  rw [show ((Hd h i d n).length==1)=false from by rw [length_Hd]; simp; omega]
  rfl

theorem gp1_Win_zero (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp1 (Win i d n) 0=Gq i := by
  show (if ((0:Int)<0) then 0 else ((Win i d n).getD 0 (0,0)).2)=Gq i
  rw [if_neg (by omega),getD_Win i d n 0 (by omega),Nat.zero_add]

/-- 相 4 の畳み込み: `Aw` は 2 列を切り出して `Q2` に降りる。 -/
theorem fold_Aw (E : Int) (n f : Nat) (hE : 1 ≤ E) (hn : 1 ≤ n) :
    Trans.Recal.red (f+1) (Aw E n)
      = Trans.Recal.jjSeq 0 1
        ++ Trans.Recal.incrFirst (Trans.Recal.red f (Q2 E (n-1))) 1 := by
  have htr : Trans.Recal.trMax (A2 2 4 E n)=1 :=
    trMax_A2_one 2 4 E n hn (by omega) (by rw [Gp_4]; omega) (by rw [Gq_4]; omega)
  have hNJ : (((1:Int)+1,(0:Int)+1) :: Trans.Recal.derp (Win 4 E n))=Q2 E (n-1) := by
    obtain ⟨u,hu⟩ : ∃ u, n=u+1 := ⟨n-1,by omega⟩
    subst hu
    show ((1:Int)+1,(0:Int)+1) :: (Win 4 E (u+1)).drop 1=Q2 E (u+1-1)
    rw [Win_drop 4 E u]
    rfl
  have key := Rows.Ladder.red_fold_single (A2 2 4 E n) f 1 0 1 (Win 4 E n)
    (isZeroP_A2 2 4 E n) (prin_Aw E n hE)
    (gp0_A2_0 2 4 E n) (gp1_A2_0 2 4 E n) htr
    (by rw [lenI_A2]; exact beq_eq_false_iff_ne.mpr (by omega))
    (brF_A2 2 4 E n hn htr (by omega) (by omega))
    (by rw [show (1:Int)+1=2 from by omega]
        exact joint_Aw E n hE hn)
    (by rw [gp1_Win_zero 4 E n hn,Gq_4,show ((1:Int)==0)=false from rfl]
        simp only [Bool.false_eq_true,if_false]
        rw [show (1:Int)+1=2 from by omega]
        exact nJ_Aw E n hE hn)
  unfold Aw
  rw [key,hNJ,show (1:Int)-0=1 from by omega]

/-- 相 3 の畳み込み: `Bw` は 2 列を切り出して `Zw` に降りる。ずらしは 2。 -/
theorem fold_Bw (D : Int) (k f : Nat) (hD : 1 ≤ D) (hk : 1 ≤ k) :
    Trans.Recal.red (f+1) (Bw D k)
      = Trans.Recal.jjSeq 0 1
        ++ Trans.Recal.incrFirst (Trans.Recal.red f (Zw D (k-1))) 2 := by
  have htr : Trans.Recal.trMax (A2 3 5 D k)=1 :=
    trMax_A2_one 3 5 D k hk (by omega) (by rw [Gp_5]; omega) (by rw [Gq_5]; omega)
  have hNJ : (((1:Int)+1,(-1:Int)+1) :: Trans.Recal.derp (Win 5 D k))=Zw D (k-1) := by
    obtain ⟨u,hu⟩ : ∃ u, k=u+1 := ⟨k-1,by omega⟩
    subst hu
    show ((1:Int)+1,(-1:Int)+1) :: (Win 5 D (u+1)).drop 1=Zw D (u+1-1)
    rw [Win_drop 5 D u]
    rw [show ((1:Int)+1)=(2:Int) from by omega,show ((-1:Int)+1)=(0:Int) from by omega]
    rfl
  have key := Rows.Ladder.red_fold_single (A2 3 5 D k) f 1 (-1) 1 (Win 5 D k)
    (isZeroP_A2 3 5 D k) (prin_Bw D k hD)
    (gp0_A2_0 3 5 D k) (gp1_A2_0 3 5 D k) htr
    (by rw [lenI_A2]; exact beq_eq_false_iff_ne.mpr (by omega))
    (brF_A2 3 5 D k hk htr (by omega) (by omega))
    (by rw [show (1:Int)+1=2 from by omega]
        exact joint_Bw D k hD hk)
    (by rw [gp1_Win_zero 5 D k hk,Gq_5,show ((0:Int)==0)=true from rfl]
        simp only [if_true])
  unfold Bw
  rw [key,hNJ,show (1:Int)-(-1)=2 from by omega]

/-- 相 2 の畳み込み: `Cw` は 3 列を切り出して `Q1` に降りる。ずらしは 0。 -/
theorem fold_Cw (G : Int) (t f : Nat) (hG : (0:Int) ≤ G) (ht : 3 ≤ t) :
    Trans.Recal.red (f+1) (Cw G t)
      = Trans.Recal.jjSeq 0 2
        ++ Trans.Recal.incrFirst (Trans.Recal.red f (Q1 (G+3) (t-3))) 0 := by
  have htr : Trans.Recal.trMax (Cw G t)=2 := trMax_Cw G t ht (by omega)
  have hNJ : (((0:Int)+1,(0:Int)+1) :: Trans.Recal.derp (Win 8 G (t-2)))
      =Q1 (G+3) (t-3) := by
    obtain ⟨u,hu⟩ : ∃ u, t=u+3 := ⟨t-3,by omega⟩
    subst hu
    show ((0:Int)+1,(0:Int)+1) :: (Win 8 G (u+3-2)).drop 1=Q1 (G+3) (u+3-3)
    rw [show u+3-2=u+1 from rfl,Win_drop 8 G u,show u+3-3=u from rfl,
      show Win 9 G u=Win 4 (G+3) u from by
        rw [show (9:Nat)=4+5 from rfl,Win_add_five]]
    rw [show ((0:Int)+1)=(1:Int) from by omega]
    rfl
  have key := Rows.Ladder.red_fold_single (Cw G t) f 2 0 0 (Win 8 G (t-2))
    (by unfold Cw; exact isZeroP_Hd_of_len _ 6 G t (by omega))
    (prin_Cw G t (by omega) (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 6 G t) (by unfold Cw; exact gp1_Hd_0 _ 6 G t) htr
    (by unfold Cw; rw [lenI_Hd]; exact beq_eq_false_iff_ne.mpr (by omega))
    (brF_Cw G t ht (by omega))
    (by rw [show (2:Int)+1=3 from by omega]
        exact joint_Cw G t (by omega) ht)
    (by rw [gp1_Win_zero 8 G (t-2) (by omega),Gq_8,show ((1:Int)==0)=false from rfl]
        simp only [Bool.false_eq_true,if_false]
        rw [show (2:Int)+1=3 from by omega]
        exact nJ_Cw G t (by omega) ht)
  rw [key,hNJ,show (0:Int)-0=0 from by omega]

#guard (List.range 6).all fun n => Trans.Recal.brF (Aw 1 (n+1))==[Win 4 1 (n+1)]
#guard (List.range 6).all fun k => Trans.Recal.brF (Bw 2 (k+1))==[Win 5 2 (k+1)]
#guard (List.range 6).all fun t => Trans.Recal.brF (Cw 0 (t+3))==[Win 8 0 (t+1)]

/-! ### Link 2, step 21: the two head steps, the base cases, and the glue. -/

theorem Win_append (i : Nat) (d : Int) (a b : Nat) :
    Win i d a++Win (i+a) d b=Win i d (a+b) := by
  induction b with
  | zero => simp [Win]
  | succ b ih =>
    rw [Win_succ (i+a) d b,← List.append_assoc,ih,show a+(b+1)=(a+b)+1 by omega,
      Win_succ i d (a+b),show b+(i+a)=(a+b)+i by omega]

theorem Win_zero_one : Win 0 0 1=([((0:Int),(0:Int))] : Trans.Recal.PS) := by decide
theorem Win_zero_two :
    Win 0 0 2=([((0:Int),(0:Int)),((1:Int),(1:Int))] : Trans.Recal.PS) := by decide
theorem Win_zero_three :
    Win 0 0 3=([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))]
      : Trans.Recal.PS) := by decide

theorem jj_one : Trans.Recal.jjSeq 0 1=([((0:Int),(0:Int)),((1:Int),(1:Int))]
    : Trans.Recal.PS) := rfl
theorem jj_two : Trans.Recal.jjSeq 0 2
    =([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))] : Trans.Recal.PS) := rfl

theorem V_eq_Q1 (m : Nat) : V m=Q1 0 (m+1) := by
  rw [V_eq_Win,Win_cons]
  show (Gp 3+0,Gq 3) :: Win 4 0 (m+1)=((1:Int),(1:Int)) :: Win 4 0 (m+1)
  rw [show Gp 3=1 from by decide,Gq_3]
  rfl

theorem gp0_Win_zero (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp0 (Win i d n) 0=Gp i+d := by
  show (if ((0:Int)<0) then 0 else ((Win i d n).getD 0 (0,0)).1)=Gp i+d
  rw [if_neg (by omega),getD_Win i d n 0 (by omega),Nat.zero_add]

theorem Win3_cons (s : Nat) : Win 3 0 (s+1)=((1:Int),(1:Int)) :: Win 4 0 s := by
  rw [Win_cons]
  show (Gp 3+0,Gq 3) :: Win 4 0 s=_
  rw [show Gp 3=1 from by decide,Gq_3]
  rfl

/-- `Q1` の段。`Aw` の答えから頭を落とす。 -/
theorem step_Q1 (e : Int) (s f : Nat) (he : 0 ≤ e)
    (h : Trans.Recal.red f (Aw (e+1) s)=RA s) :
    Trans.Recal.red (f+1) (Q1 e s)=Win 3 0 (s+1) := by
  have hA : Trans.Recal.red f (((0:Int),(0:Int)) :: Y ((1:Int)+1) 4 (e+1) s)
      =((0:Int),(0:Int)) :: Win 3 0 (s+1) := by
    rw [Win3_cons,show ((1:Int)+1)=(2:Int) from by omega]
    exact h
  exact red_Y_of_A 1 4 e s f (Win 3 0 (s+1)) (by decide) (prin_Q1 e s he) hA
    (by rw [length_Win]; omega) (prin_Win_three s)
    (by rw [gp0_Win_zero 3 0 (s+1) (by omega),gp1_Win_zero 3 0 (s+1) (by omega),
      show Gp 3=1 from by decide,Gq_3]
        omega)

/-- `Q2` の段。 -/
theorem step_Q2 (E : Int) (k f : Nat) (hE : 0 ≤ E)
    (h : Trans.Recal.red f (Bw (E+1) k)=((0:Int),(0:Int)) :: RQ k) :
    Trans.Recal.red (f+1) (Q2 E k)=RQ k := by
  have hA : Trans.Recal.red f (((0:Int),(0:Int)) :: Y ((2:Int)+1) 5 (E+1) k)
      =((0:Int),(0:Int)) :: RQ k := by
    rw [show ((2:Int)+1)=(3:Int) from by omega]
    exact h
  exact red_Y_of_A 2 5 E k f (RQ k) (by decide) (prin_Q2 E k hE) hA
    (by unfold RQ; rw [List.length_cons]; omega) (prin_RQ k)
    (by show Trans.Recal.gp0 (Hd ((1:Int),(1:Int)) 5 (-1) k) 0
          =Trans.Recal.gp1 (Hd ((1:Int),(1:Int)) 5 (-1) k) 0
        rw [gp0_Hd_0,gp1_Hd_0])

/-- `Zw` の段。畳み込みではなく、頭を 0 に正規化して降りるだけ。 -/
theorem step_Zw (D : Int) (t f : Nat) (hD : (-1:Int) ≤ D) (ht : 1 ≤ t) :
    Trans.Recal.red (f+1) (Zw D t)=Trans.Recal.red f (Cw (D-2) t) :=
  red_Zr_step 2 6 D t f ht (by decide) (prin_Zw D t hD ht)

/-! #### 底 -/

theorem base_Aw (E : Int) (f : Nat) : Trans.Recal.red (f+1) (Aw E 0)=RA 0 := by
  have h := Rows.Ladder.red_jj (A2 2 4 E 0) f (isZeroP_A2 2 4 E 0)
    (isPrincipalP_A2 2 4 E 0 (by omega) (by omega) (fun t _ ht => absurd ht (by omega)))
    (gp0_A2_0 2 4 E 0) (gp1_A2_0 2 4 E 0)
    (by rw [trMax_A2_zero 2 4 E (by omega),lenI_A2]; omega)
  unfold Aw
  rw [h,lenI_A2,show ((0:Nat):Int)+2-1=1 from by omega,jj_one]
  rfl

theorem base_Bw (D : Int) (f : Nat) :
    Trans.Recal.red (f+1) (Bw D 0)=((0:Int),(0:Int)) :: RQ 0 := by
  have h := Rows.Ladder.red_jj (A2 3 5 D 0) f (isZeroP_A2 3 5 D 0)
    (isPrincipalP_A2 3 5 D 0 (by omega) (by omega) (fun t _ ht => absurd ht (by omega)))
    (gp0_A2_0 3 5 D 0) (gp1_A2_0 3 5 D 0)
    (by rw [trMax_A2_zero 3 5 D (by omega),lenI_A2]; omega)
  unfold Bw
  rw [h,lenI_A2,show ((0:Nat):Int)+2-1=1 from by omega,jj_one]
  rfl

theorem base_Zw (D : Int) (f : Nat) : Trans.Recal.red (f+1) (Zw D 0)=Win 0 0 1 := by
  rw [Rows.Ladder.red_zeroP _ f (by rfl),Win_zero_one]
  rfl

theorem base_Cw_one (G : Int) (f : Nat) (hG : (-3:Int) ≤ G) :
    Trans.Recal.red (f+1) (Cw G 1)=Win 0 0 2 := by
  have h := Rows.Ladder.red_jj (Cw G 1) f
    (by unfold Cw; exact isZeroP_Hd_of_len _ 6 G 1 (by omega))
    (prin_Cw G 1 hG (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 6 G 1) (by unfold Cw; exact gp1_Hd_0 _ 6 G 1)
    (by rw [trMax_Cw_one G hG]; unfold Cw; rw [lenI_Hd]; omega)
  rw [h,show Trans.Recal.lenI (Cw G 1)=2 from by unfold Cw; rw [lenI_Hd]; omega,
    show (2:Int)-1=1 from by omega,jj_one,Win_zero_two]

theorem base_Cw_two (G : Int) (f : Nat) (hG : (-3:Int) ≤ G) :
    Trans.Recal.red (f+1) (Cw G 2)=Win 0 0 3 := by
  have h := Rows.Ladder.red_jj (Cw G 2) f
    (by unfold Cw; exact isZeroP_Hd_of_len _ 6 G 2 (by omega))
    (prin_Cw G 2 hG (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 6 G 2) (by unfold Cw; exact gp1_Hd_0 _ 6 G 2)
    (by rw [trMax_Cw_two G hG]; unfold Cw; rw [lenI_Hd]; omega)
  rw [h,show Trans.Recal.lenI (Cw G 2)=3 from by unfold Cw; rw [lenI_Hd]; omega,
    show (3:Int)-1=2 from by omega,jj_two,Win_zero_three]

/-! #### 貼り合わせ -/

theorem glue_Aw (k : Nat) :
    Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst (RQ k) 1=RA (k+1) := by
  unfold RQ RA
  rw [jj_one]
  show ([((0:Int),(0:Int)),((1:Int),(1:Int))] : Trans.Recal.PS)
    ++(((1:Int)+1,(1:Int)) :: Trans.Recal.incrFirst (Win 5 (-1) k) 1)
    =((0:Int),(0:Int)) :: ((1:Int),(1:Int)) :: Win 4 0 (k+1)
  rw [incrFirst_Win,show ((-1:Int)+1)=(0:Int) from by omega,
    show ((1:Int)+1)=(2:Int) from by omega,Win_cons 4 0 k,Gp_4,Gq_4,
    show Win (4+1) 0 k=Win 5 0 k from rfl,show ((2:Int)+0)=(2:Int) from by omega]
  rfl

theorem glue_Bw (k : Nat) :
    Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst (Win 0 0 k) 2
      =((0:Int),(0:Int)) :: RQ k := by
  unfold RQ
  rw [jj_one,incrFirst_Win,show ((0:Int)+2)=(2:Int) from by omega,
    show Win 5 (-1) k=Win 0 2 k from by
      rw [show (5:Nat)=0+5 from rfl,Win_add_five,show ((-1:Int)+3)=(2:Int) from by omega]]
  rfl

theorem glue_Cw (t : Nat) (ht : 2 ≤ t) :
    Trans.Recal.jjSeq 0 2++Trans.Recal.incrFirst (Win 3 0 (t-2)) 0=Win 0 0 (t+1) := by
  rw [jj_two,incrFirst_Win,show ((0:Int)+0)=(0:Int) from by omega,← Win_zero_three,
    show (3:Nat)=0+3 from rfl,Win_append 0 0 3 (t-2),show 3+(t-2)=t+1 by omega]

/-! ### Link 2, step 22: the cycle closes.

`Aw E n` reduces to `RA n` — the shift `E` never reaches the answer.  The recursion
descends five columns and raises the shift by three per turn, so the induction is on
`n` with step five, and the five residues are the base cases. -/

theorem red_Aw_of_Bw (E : Int) (n f : Nat) (hE : 1 ≤ E) (hn : 1 ≤ n)
    (h : Trans.Recal.red f (Bw (E+1) (n-1))=((0:Int),(0:Int)) :: RQ (n-1)) :
    Trans.Recal.red (f+2) (Aw E n)=RA n := by
  rw [show f+2=(f+1)+1 by omega,fold_Aw E n (f+1) hE hn,
    step_Q2 E (n-1) f (by omega) h,glue_Aw (n-1),show n-1+1=n by omega]

theorem red_Bw_of_Zw (D : Int) (k f : Nat) (hD : 1 ≤ D) (hk : 1 ≤ k)
    (h : Trans.Recal.red f (Zw D (k-1))=Win 0 0 k) :
    Trans.Recal.red (f+1) (Bw D k)=((0:Int),(0:Int)) :: RQ k := by
  rw [fold_Bw D k f hD hk,h,glue_Bw k]

theorem red_Cw_of_Q1 (G : Int) (t f : Nat) (hG : (0:Int) ≤ G) (ht : 3 ≤ t)
    (h : Trans.Recal.red f (Q1 (G+3) (t-3))=Win 3 0 (t-2)) :
    Trans.Recal.red (f+1) (Cw G t)=Win 0 0 (t+1) := by
  rw [fold_Cw G t f hG ht,h,glue_Cw t (by omega)]

/-- **輪が閉じる。** `Aw` の答えはずらしに依らない。 -/
theorem red_Aw_all (n : Nat) : ∀ (E : Int) (f : Nat), 1 ≤ E →
    Trans.Recal.red (2*n+f+6) (Aw E n)=RA n := by
  refine Nat.strongRecOn n ?_
  intro n ih E f hE
  rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ 5 ≤ n by omega) with rfl|rfl|rfl|rfl|rfl|h5
  · rw [show 2*0+f+6=(f+5)+1 by omega]
    exact base_Aw E (f+5)
  · rw [show 2*1+f+6=((f+5)+1)+2 by omega]
    exact red_Aw_of_Bw E 1 ((f+5)+1) hE (by omega) (base_Bw (E+1) (f+5))
  · rw [show 2*2+f+6=(((f+6)+1)+1)+2 by omega]
    refine red_Aw_of_Bw E 2 (((f+6)+1)+1) hE (by omega) ?_
    exact red_Bw_of_Zw (E+1) 1 ((f+6)+1) (by omega) (by omega) (base_Zw (E+1) (f+6))
  · rw [show 2*3+f+6=((((f+7)+1)+1)+1)+2 by omega]
    refine red_Aw_of_Bw E 3 ((((f+7)+1)+1)+1) hE (by omega) ?_
    refine red_Bw_of_Zw (E+1) 2 (((f+7)+1)+1) (by omega) (by omega) ?_
    rw [step_Zw (E+1) 1 ((f+7)+1) (by omega) (by omega),
      show E+1-2=E-1 from by omega]
    exact base_Cw_one (E-1) (f+7) (by omega)
  · rw [show 2*4+f+6=((((f+9)+1)+1)+1)+2 by omega]
    refine red_Aw_of_Bw E 4 ((((f+9)+1)+1)+1) hE (by omega) ?_
    refine red_Bw_of_Zw (E+1) 3 (((f+9)+1)+1) (by omega) (by omega) ?_
    rw [step_Zw (E+1) 2 ((f+9)+1) (by omega) (by omega),
      show E+1-2=E-1 from by omega]
    exact base_Cw_two (E-1) (f+9) (by omega)
  · obtain ⟨r,rfl⟩ : ∃ r, n=r+5 := ⟨n-5,by omega⟩
    have hIH : Trans.Recal.red (2*r+(f+4)+6) (Aw (E+3) r)=RA r :=
      ih r (by omega) (E+3) (f+4) (by omega)
    have hQ1 : Trans.Recal.red ((2*r+(f+4)+6)+1) (Q1 (E+2) r)=Win 3 0 (r+1) := by
      refine step_Q1 (E+2) r (2*r+(f+4)+6) (by omega) ?_
      rw [show E+2+1=E+3 from by omega]
      exact hIH
    have hCw : Trans.Recal.red ((2*r+(f+4)+6)+2) (Cw (E-1) (r+3))=Win 0 0 (r+4) := by
      refine red_Cw_of_Q1 (E-1) (r+3) ((2*r+(f+4)+6)+1) (by omega) (by omega) ?_
      rw [show E-1+3=E+2 from by omega,show r+3-3=r from by omega,
        show r+3-2=r+1 from by omega]
      exact hQ1
    have hZw : Trans.Recal.red ((2*r+(f+4)+6)+3) (Zw (E+1) (r+3))=Win 0 0 (r+4) := by
      rw [show (2*r+(f+4)+6)+3=((2*r+(f+4)+6)+2)+1 by omega,
        step_Zw (E+1) (r+3) ((2*r+(f+4)+6)+2) (by omega) (by omega),
        show E+1-2=E-1 from by omega]
      exact hCw
    have hBw : Trans.Recal.red ((2*r+(f+4)+6)+4) (Bw (E+1) (r+4))
        =((0:Int),(0:Int)) :: RQ (r+4) := by
      refine red_Bw_of_Zw (E+1) (r+4) ((2*r+(f+4)+6)+3) (by omega) (by omega) ?_
      rw [show r+4-1=r+3 from by omega]
      exact hZw
    rw [show 2*(r+5)+f+6=((2*r+(f+4)+6)+4)+2 by omega]
    refine red_Aw_of_Bw E (r+5) ((2*r+(f+4)+6)+4) hE (by omega) ?_
    rw [show r+5-1=r+4 from by omega]
    exact hBw

/-- `V m` は `red` の不動点。 -/
theorem red_V (m f : Nat) : Trans.Recal.red (2*m+f+9) (V m)=V m := by
  have h : Trans.Recal.red (2*(m+1)+f+6) (Aw ((0:Int)+1) (m+1))=RA (m+1) :=
    red_Aw_all (m+1) ((0:Int)+1) f (by omega)
  have key : Trans.Recal.red ((2*(m+1)+f+6)+1) (Q1 0 (m+1))=Win 3 0 (m+2) := by
    have h2 := step_Q1 0 (m+1) (2*(m+1)+f+6) (by omega) h
    rwa [show m+1+1=m+2 by omega] at h2
  rw [V_eq_Q1 m,show 2*m+f+9=(2*(m+1)+f+6)+1 by omega,key,← V_eq_Win]
  exact V_eq_Q1 m

theorem red_L (m f : Nat) : Trans.Recal.red (2*m+f+10) (L m)=L m := by
  rw [show 2*m+f+10=(2*m+f+9)+1 by omega,red_L_step m (2*m+f+9),red_V m f,
    ← L_cons_V]

/-- **リンク 2 の前半: 梯子は既約。** -/
theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  unfold Trans.Recal.redP
  obtain ⟨f,hf⟩ : ∃ f, Trans.Recal.redFuel (L m)=2*m+f+10 := by
    refine ⟨Trans.Recal.redFuel (L m)-(2*m+10),?_⟩
    have : 40+4*((L m).length+Trans.Recal.maxE (L m)) ≤ Trans.Recal.redFuel (L m) := by
      unfold Trans.Recal.redFuel
      omega
    rw [length_L] at this
    omega
  rw [hf]
  exact red_L m f

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  simp

#guard (List.range 12).all fun m => Trans.Recal.isReducedP (L m)
#print axioms isReducedP_L
#print axioms red_Aw_all

/-! ### Link 2, step 23: admissibility.

`isAdm (L m) j` does not depend on `m` except through the range: an index is
inadmissible exactly when it and its successor are both row-one parents of their
predecessors, and on this ladder that happens only at `j ≡ 1 (mod 5)`. -/

theorem fpar0_L_prev_hit (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5) (h0 : Gp (j-1)<Gp j) :
    Trans.Recal.fpar0 (L m) ((j:Nat):Int) ((j-1:Nat):Int)=((j-1:Nat):Int) := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m j hjm,
    show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega,
    Rows.Ladder.fpar0Aux_step,if_neg (by omega),gp0_L m (j-1) (by omega),if_pos h0]

theorem fpar0_L_prev_miss (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h0 : ¬(Gp (j-1)<Gp j)) :
    Trans.Recal.fpar0 (L m) ((j:Nat):Int) ((j-1:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m j hjm,
    show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega,
    show m+5+1=(m+5)+1 from rfl,
    Rows.Ladder.fpar0Aux_step,if_neg (by omega),gp0_L m (j-1) (by omega),if_neg h0]
  obtain ⟨g,hg⟩ : ∃ g, m+5=g+1 := ⟨m+4,by omega⟩
  rw [hg,Rows.Ladder.fpar0Aux_step,if_pos (by omega)]

theorem fpar0_L_self_stop (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5) :
    Trans.Recal.fpar0 (L m) ((j-1:Nat):Int) ((j-1:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,
    show m+5+1=(m+5)+1 from rfl,
    Rows.Ladder.fpar0Aux_step,if_pos (by omega)]

/-- 行 1 の親、直前の添字に対して。`Gp` と `Gq` がどちらも下がるときだけ当たる。 -/
theorem fpar1_L_prev_hit (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h0 : Gp (j-1)<Gp j) (h1 : Gq (j-1)<Gq j) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)=((j-1:Nat):Int) := by
  rw [Rows.Ladder.fpar1_unfold (L m) _ _ (by rw [lenI_L]; omega),length_L,
    show m+5+1=(m+5)+1 from rfl,
    Rows.Ladder.fpar1Aux_step,fpar0_L_prev_hit m j hj hjm h0,if_neg (by omega),
    gp1_L m (j-1) (by omega),gp1_L m j hjm,if_pos h1]

theorem fpar1_L_prev_miss (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h0 : Gp (j-1)<Gp j) (h1 : ¬(Gq (j-1)<Gq j)) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)=-1 := by
  rw [Rows.Ladder.fpar1_unfold (L m) _ _ (by rw [lenI_L]; omega),length_L,
    show m+5+1=(m+5)+1 from rfl,
    Rows.Ladder.fpar1Aux_step,fpar0_L_prev_hit m j hj hjm h0,if_neg (by omega),
    gp1_L m (j-1) (by omega),gp1_L m j hjm,if_neg h1]
  obtain ⟨g,hg⟩ : ∃ g, m+5=g+1 := ⟨m+4,by omega⟩
  rw [hg,Rows.Ladder.fpar1Aux_step,fpar0_L_self_stop m j hj hjm,if_pos (by omega)]

theorem fpar1_L_prev_nodrop (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h0 : ¬(Gp (j-1)<Gp j)) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)=-1 := by
  rw [Rows.Ladder.fpar1_unfold (L m) _ _ (by rw [lenI_L]; omega),length_L,
    show m+5+1=(m+5)+1 from rfl,
    Rows.Ladder.fpar1Aux_step,fpar0_L_prev_miss m j hj hjm h0,if_pos (by omega)]

#guard (List.range 12).all fun m => (List.range (m+5)).all fun j =>
  (j==0) ||
    (Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)
      == (if Gp (j-1)<Gp j ∧ Gq (j-1)<Gq j then ((j-1:Nat):Int) else -1))

theorem Gq_lt_of_r1 (j : Nat) (h : j%5=1) : Gq (j-1)<Gq j := by
  unfold Gq
  rw [if_pos (by omega),if_neg (by omega),if_neg (by omega)]
  omega

theorem Gq_lt_of_r2 (j : Nat) (h : j%5=2) : Gq (j-1)<Gq j := by
  unfold Gq
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  omega

theorem Gq_ge_of_r4 (j : Nat) (h : j%5=4) : ¬(Gq (j-1)<Gq j) := by
  unfold Gq
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  omega

theorem Gq_ge_of_r0 (j : Nat) (hj : 1 ≤ j) (h : j%5=0) : ¬(Gq (j-1)<Gq j) := by
  unfold Gq
  rw [if_pos h,if_neg (by omega),if_neg (by omega)]
  omega

/-- **行 1 の親は残余だけで決まる。** -/
theorem fpar1_L_prev (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)
      = if j%5=1 ∨ j%5=2 then ((j-1:Nat):Int) else -1 := by
  rcases (show j%5=0 ∨ j%5=1 ∨ j%5=2 ∨ j%5=3 ∨ j%5=4 by omega) with h|h|h|h|h
  · rw [if_neg (by omega)]
    exact fpar1_L_prev_miss m j hj hjm (Gp_lt_step j hj (by omega)) (Gq_ge_of_r0 j hj h)
  · rw [if_pos (by omega)]
    exact fpar1_L_prev_hit m j hj hjm (Gp_lt_step j hj (by omega)) (Gq_lt_of_r1 j h)
  · rw [if_pos (by omega)]
    exact fpar1_L_prev_hit m j hj hjm (Gp_lt_step j hj (by omega)) (Gq_lt_of_r2 j h)
  · rw [if_neg (by omega)]
    exact fpar1_L_prev_nodrop m j hj hjm (by
      have := (Gp_three j h).2.2
      omega)
  · rw [if_neg (by omega)]
    exact fpar1_L_prev_miss m j hj hjm (Gp_lt_step j hj (by omega)) (Gq_ge_of_r4 j h)

theorem isParentP_L_prev_false (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h : ¬(j%5=1 ∨ j%5=2)) :
    Trans.Recal.isParentP (L m) 1 ((j:Nat):Int) (((j:Nat):Int)-1)=false := by
  rw [show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega]
  refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
  rw [fpar1_L_prev m j hj hjm,if_neg h]

theorem isParentP_L_prev_true (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h : j%5=1 ∨ j%5=2) :
    Trans.Recal.isParentP (L m) 1 ((j:Nat):Int) (((j:Nat):Int)-1)=true := by
  rw [show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega]
  refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega) (by rw [lenI_L]; omega) ?_
  rw [fpar1_L_prev m j hj hjm,if_pos h]

/-- 残余が 1 でない添字は入場可能。 -/
theorem isAdm_L_true (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h : ¬(j%5=1 ∨ j%5=2)) : Trans.Recal.isAdm (L m) ((j:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((j:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  rw [isParentP_L_prev_false m j hj hjm h,Bool.false_and]
  rfl

/-- 残余が 1 の添字は入場不可 — 次の列がまだあるとき。 -/
theorem isAdm_L_false (m j : Nat) (hj : 1 ≤ j) (h : j%5=1) (hjm : j+1<m+5) :
    Trans.Recal.isAdm (L m) ((j:Nat):Int)=false := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((j:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  rw [isParentP_L_prev_true m j hj (by omega) (Or.inl h),
    show ((j:Nat):Int)+1=(((j+1:Nat)):Int) from by omega,
    show ((j:Nat):Int)=(((j+1:Nat)):Int)-1 from by omega,
    isParentP_L_prev_true m (j+1) (by omega) (by omega) (Or.inr (by omega))]
  rfl

theorem adm_L_self (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+5)
    (h : ¬(j%5=1 ∨ j%5=2)) :
    Trans.Recal.adm (L m) ((j:Nat):Int)=((j:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L,show m+5+2=(m+5+1)+1 from rfl,Rows.Ladder.admAux_step,if_neg (by omega),
    isAdm_L_true m j hj hjm h,if_pos rfl]

theorem adm_L_down (m j : Nat) (hj : 2 ≤ j) (h : j%5=1) (hjm : j+1<m+5) :
    Trans.Recal.adm (L m) ((j:Nat):Int)=((j-1:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L,show m+5+2=((m+5)+1)+1 from rfl,Rows.Ladder.admAux_step,if_neg (by omega),
    isAdm_L_false m j (by omega) h hjm]
  simp only [Bool.false_eq_true,if_false]
  rw [show m+6=(m+5)+1 from rfl,show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega,
    Rows.Ladder.admAux_step,if_neg (by omega),
    isAdm_L_true m (j-1) (by omega) (by omega) (by omega),if_pos rfl]

#guard (List.range 12).all fun m => (List.range (m+4)).all fun j =>
  (j==0) || (Trans.Recal.isAdm (L m) ((j:Nat):Int)
    == !(decide (j%5=1)))
#guard (List.range 12).all fun m => (List.range (m+4)).all fun j =>
  (j==0) || (Trans.Recal.adm (L m) ((j:Nat):Int)
    == (if j%5=1 then ((j-1:Nat):Int) else ((j:Nat):Int)))

/-! ### Link 2, step 24: the type of each phase, and its `c2`.

`j0`, the transition type and `c2` all depend only on `k mod 5`:

    r   j1    j0     ty   adm j0   c1            c2
    0   k+4   k+3    3    k+3      D1 0          D1 (D1 0)
    1   k+4   k+3    1    k+3      D1 0          D1 (D0 0)
    2   k+4   k+3    6    k+3      D0 0          D0 (D1 0)
    3   k+4   k+3    6    k+2      D0 (D1 0)     D0 (D2 0)
    4   k+4   k+1    5    k+1      D0 (D2 0)     D0 (D2 0 + D1 0)
-/

theorem j0_L_not4 (k : Nat) (h : k%5 ≠ 4) :
    Trans.Recal.fpar (L k) 0 ((k+4:Nat):Int) 0=((k+3:Nat):Int) := by
  rw [fpar_L_zero k (k+4) (by omega)]
  unfold parL
  rw [if_neg (by omega),if_neg (by omega)]
  omega

theorem j0_L_four (k : Nat) (h : k%5=4) :
    Trans.Recal.fpar (L k) 0 ((k+4:Nat):Int) 0=((k+1:Nat):Int) := by
  rw [fpar_L_zero k (k+4) (by omega)]
  unfold parL
  rw [if_neg (by omega),if_pos (by omega)]
  omega

theorem Gq_r0 (j : Nat) (h : j%5=0) : Gq j=0 := by
  unfold Gq; rw [if_pos h]
theorem Gq_r1 (j : Nat) (h : j%5=1) : Gq j=1 := by
  unfold Gq; rw [if_neg (by omega),if_neg (by omega)]
theorem Gq_r2 (j : Nat) (h : j%5=2) : Gq j=2 := by
  unfold Gq; rw [if_neg (by omega),if_pos h]
theorem Gq_r3 (j : Nat) (h : j%5=3) : Gq j=1 := by
  unfold Gq; rw [if_neg (by omega),if_neg (by omega)]
theorem Gq_r4 (j : Nat) (h : j%5=4) : Gq j=1 := by
  unfold Gq; rw [if_neg (by omega),if_neg (by omega)]

theorem transType_L_r0 (k : Nat) (h : k%5=0) :
    Trans.Recal.transTypeMain (L k) ((k+3:Nat):Int) ((k+4:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+4) (by omega),gp1_L k (k+3) (by omega),
    Gq_r4 (k+4) (by omega),Gq_r3 (k+3) (by omega),
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_pos (by omega),isAdm_L_true k (k+3) (by omega) (by omega) (by omega),if_pos rfl]

theorem transType_L_r1 (k : Nat) (h : k%5=1) :
    Trans.Recal.transTypeMain (L k) ((k+3:Nat):Int) ((k+4:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+4) (by omega),Gq_r0 (k+4) (by omega),
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [isAdm_L_true k (k+3) (by omega) (by omega) (by omega),if_pos rfl]

theorem transType_L_r2 (k : Nat) (h : k%5=2) :
    Trans.Recal.transTypeMain (L k) ((k+3:Nat):Int) ((k+4:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+4) (by omega),gp1_L k (k+3) (by omega),
    Gq_r1 (k+4) (by omega),Gq_r0 (k+3) (by omega),
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_neg (by omega),if_neg (by omega)]

theorem transType_L_r3 (k : Nat) (h : k%5=3) :
    Trans.Recal.transTypeMain (L k) ((k+3:Nat):Int) ((k+4:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+4) (by omega),gp1_L k (k+3) (by omega),
    Gq_r2 (k+4) (by omega),Gq_r1 (k+3) (by omega),
    show ((2:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_neg (by omega),if_neg (by omega)]

theorem transType_L_r4 (k : Nat) (h : k%5=4) :
    Trans.Recal.transTypeMain (L k) ((k+1:Nat):Int) ((k+4:Nat):Int)=5 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+4) (by omega),gp1_L k (k+1) (by omega),
    Gq_r3 (k+4) (by omega),Gq_r0 (k+1) (by omega),
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_neg (by omega),if_pos (by omega)]

theorem adm_L_r0 (k : Nat) (h : k%5=0) :
    Trans.Recal.adm (L k) ((k+3:Nat):Int)=((k+3:Nat):Int) :=
  adm_L_self k (k+3) (by omega) (by omega) (by omega)

theorem adm_L_r1 (k : Nat) (h : k%5=1) :
    Trans.Recal.adm (L k) ((k+3:Nat):Int)=((k+3:Nat):Int) :=
  adm_L_self k (k+3) (by omega) (by omega) (by omega)

theorem adm_L_r2 (k : Nat) (h : k%5=2) :
    Trans.Recal.adm (L k) ((k+3:Nat):Int)=((k+3:Nat):Int) :=
  adm_L_self k (k+3) (by omega) (by omega) (by omega)

theorem adm_L_r3 (k : Nat) (h : k%5=3) :
    Trans.Recal.adm (L k) ((k+3:Nat):Int)=((k+2:Nat):Int) := by
  have := adm_L_down k (k+3) (by omega) (by omega) (by omega)
  rwa [show k+3-1=k+2 from rfl] at this

theorem adm_L_r4 (k : Nat) (h : k%5=4) :
    Trans.Recal.adm (L k) ((k+1:Nat):Int)=((k+1:Nat):Int) :=
  adm_L_self k (k+1) (by omega) (by omega) (by omega)

theorem mkC2_L_r0 (k : Nat) (h : k%5=0) :
    Trans.Recal.mkC2 (L k) ((k+3:Nat):Int) ((k+4:Nat):Int) 3 D1z=D11z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+4) (by omega),Gq_r4 (k+4) (by omega)]
  rfl

theorem mkC2_L_r1 (k : Nat) (h : k%5=1) :
    Trans.Recal.mkC2 (L k) ((k+3:Nat):Int) ((k+4:Nat):Int) 1 D1z
      =Trans.Dict.BT.D 1 D0z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+4) (by omega),Gq_r0 (k+4) (by omega)]
  rfl

theorem mkC2_L_r2 (k : Nat) (h : k%5=2) :
    Trans.Recal.mkC2 (L k) ((k+3:Nat):Int) ((k+4:Nat):Int) 6 D0z
      =Trans.Dict.BT.D 0 D1z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+4) (by omega),Gq_r1 (k+4) (by omega)]
  rfl

theorem mkC2_L_r3 (k : Nat) (h : k%5=3) :
    Trans.Recal.mkC2 (L k) ((k+3:Nat):Int) ((k+4:Nat):Int) 6
      (Trans.Dict.BT.D 0 D1z)=Trans.Dict.BT.D 0 D2z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+4) (by omega),Gq_r2 (k+4) (by omega)]
  rfl

theorem mkC2_L_r4 (k : Nat) (h : k%5=4) :
    Trans.Recal.mkC2 (L k) ((k+1:Nat):Int) ((k+4:Nat):Int) 5
      (Trans.Dict.BT.D 0 D2z)=Trans.Dict.BT.D 0 (Trans.Dict.BT.sum D2z D1z) := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L k (k+4) (by omega),Gq_r3 (k+4) (by omega)]
  rfl

/-! ### Link 2, step 25: the replacement inside the reader output.

`LBT m = D 0 (W (m/5) (Part (m%5)))`, and the rightmost spine of `W` descends four
constructors per complete block.  So the mark always lands inside `Part`, and each
phase is one replacement there. -/

theorem repl_D0W : ∀ (a f r : Nat) (b bb c cc : Trans.Dict.BT),
    (∀ g : Nat, r ≤ g → Trans.Recal.replMark g (.D 0 b) c cc=some (.D 0 bb)) →
    (∀ n : Nat, ((Trans.Dict.BT.D 0 (W (n+1) b))==c)=false
      ∧ ((Trans.Dict.BT.D 1 (.D 1 (.D 0 (W n b))))==c)=false
      ∧ ((Trans.Dict.BT.D 1 (.D 0 (W n b)))==c)=false) →
    5*a+r ≤ f →
    Trans.Recal.replMark f (.D 0 (W a b)) c cc=some (.D 0 (W a bb))
  | 0,f,r,b,bb,c,cc,hbase,_,hf => hbase f (by simpa using hf)
  | a+1,f,r,b,bb,c,cc,hbase,hne,hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+5 := ⟨f-5,by omega⟩
    change Trans.Recal.replMark (g+5)
      (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 (W a b)))))) c cc=
      some (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 (W a bb))))))
    rw [show g+5=(g+4)+1 by omega,Trans.Recal.replMark]
    have hn:=(hne a).1
    change ((Trans.Dict.BT.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 (W a b))))))==c)=false at hn
    rw [hn]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+4=(g+3)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum D2z (.D 1 (.D 1 (.D 0 (W a b)))))=
      [D2z,.D 1 (.D 1 (.D 0 (W a b)))] from rfl]
    change ((Trans.Recal.replMark (g+3) (.D 1 (.D 1 (.D 0 (W a b)))) c cc).map
      (fun x=>Trans.Dict.BT.sum D2z x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.replMark,(hne a).2.1]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark,(hne a).2.2]
    simp only [Bool.false_eq_true,if_false]
    change ((((Trans.Recal.replMark (g+1) (.D 0 (W a b)) c cc).map
      (fun x=>Trans.Dict.BT.D 1 x)).map (fun x=>Trans.Dict.BT.D 1 x)).map
      (fun x=>Trans.Dict.BT.sum D2z x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [repl_D0W a (g+1) r b bb c cc hbase hne (by omega)]
    rfl

theorem W_add (a b : Nat) (c : Trans.Dict.BT) : W a (W b c)=W (a+b) c := by
  induction a with
  | zero => simp [W]
  | succ a ih =>
    simp only [W,ih]
    rw [show a+1+b=(a+b)+1 by omega,W]

theorem LBT_r (a r : Nat) (hr : r<5) : LBT (5*a+r)=.D 0 (W a (Part r)) := by
  unfold LBT
  rw [show (5*a+r)/5=a by omega,show (5*a+r)%5=r by omega]

theorem repl_LBT_r0 (a f : Nat) (hf : 5*a+4 ≤ f) :
    Trans.Recal.replMark f (LBT (5*a)) D1z (.D 1 D0z)=some (LBT (5*a+1)) := by
  rw [show 5*a=5*a+0 from rfl,LBT_r a 0 (by omega),LBT_r a 1 (by omega)]
  refine repl_D0W a f 4 (Part 0) (Part 1) D1z (.D 1 D0z) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+4 := ⟨g-4,by omega⟩
    change Trans.Recal.replMark (h+4)
      (.D 0 (.sum D2z (.D 1 (.D 1 Trans.Dict.BT.zero)))) D1z (.D 1 D0z)=
      some (.D 0 (.sum D2z (.D 1 (.D 1 D0z))))
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum D2z (.D 1 (.D 1 Trans.Dict.BT.zero))))==D1z)
        =false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum D2z (.D 1 (.D 1 Trans.Dict.BT.zero)))
        =[D2z,.D 1 (.D 1 Trans.Dict.BT.zero)] from rfl]
    change ((Trans.Recal.replMark (h+2) (.D 1 (.D 1 Trans.Dict.BT.zero)) D1z
      (.D 1 D0z)).map (fun x=>Trans.Dict.BT.sum D2z x)).map
        (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 1 Trans.Dict.BT.zero))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change (((Trans.Recal.replMark (h+1) D1z D1z (.D 1 D0z)).map
      (fun x=>Trans.Dict.BT.D 1 x)).map (fun x=>Trans.Dict.BT.sum D2z x)).map
        (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [G1.replMark_self (h+1) 1 .zero (.D 1 D0z) (by omega)]
    rfl
  · intro n
    refine ⟨rfl,rfl,?_⟩
    cases n <;> rfl

#guard (List.range 6).all fun a => Trans.Recal.replMark 60 (LBT (5*a)) D1z
  (Trans.Dict.BT.D 1 D0z)==some (LBT (5*a+1))
#guard (List.range 6).all fun a => Trans.Recal.replMark 60 (LBT (5*a+1)) D0z
  (Trans.Dict.BT.D 0 D1z)==some (LBT (5*a+2))
#guard (List.range 6).all fun a => Trans.Recal.replMark 60 (LBT (5*a+2))
  (Trans.Dict.BT.D 0 D1z) (Trans.Dict.BT.D 0 D2z)==some (LBT (5*a+3))
#guard (List.range 6).all fun a => Trans.Recal.replMark 60 (LBT (5*a+3))
  (Trans.Dict.BT.D 0 D2z) (Trans.Dict.BT.D 0 (.sum D2z D1z))==some (LBT (5*a+4))
#guard (List.range 6).all fun a => Trans.Recal.replMark 60 (LBT (5*a+4)) D1z D11z
  ==some (LBT (5*a+5))

theorem repl_LBT_r1 (a f : Nat) (hf : 5*a+5 ≤ f) :
    Trans.Recal.replMark f (LBT (5*a+1)) D0z (.D 0 D1z)=some (LBT (5*a+2)) := by
  rw [LBT_r a 1 (by omega),LBT_r a 2 (by omega)]
  refine repl_D0W a f 5 (Part 1) (Part 2) D0z (.D 0 D1z) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
    change Trans.Recal.replMark (h+5)
      (.D 0 (.sum D2z (.D 1 (.D 1 D0z)))) D0z (.D 0 D1z)=
      some (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 D1z)))))
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum D2z (.D 1 (.D 1 D0z))))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum D2z (.D 1 (.D 1 D0z)))
        =[D2z,.D 1 (.D 1 D0z)] from rfl]
    change ((Trans.Recal.replMark (h+3) (.D 1 (.D 1 D0z)) D0z (.D 0 D1z)).map
      (fun x=>Trans.Dict.BT.sum D2z x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 1 D0z))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 D0z)==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change ((((Trans.Recal.replMark (h+1) D0z D0z (.D 0 D1z)).map
      (fun x=>Trans.Dict.BT.D 1 x)).map (fun x=>Trans.Dict.BT.D 1 x)).map
      (fun x=>Trans.Dict.BT.sum D2z x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [G1.replMark_self (h+1) 0 .zero (.D 0 D1z) (by omega)]
    rfl
  · intro n
    exact ⟨rfl,rfl,rfl⟩

theorem repl_LBT_r2 (a f : Nat) (hf : 5*a+5 ≤ f) :
    Trans.Recal.replMark f (LBT (5*a+2)) (.D 0 D1z) (.D 0 D2z)=some (LBT (5*a+3)) := by
  rw [LBT_r a 2 (by omega),LBT_r a 3 (by omega)]
  refine repl_D0W a f 5 (Part 2) (Part 3) (.D 0 D1z) (.D 0 D2z) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
    change Trans.Recal.replMark (h+5)
      (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 D1z))))) (.D 0 D1z) (.D 0 D2z)=
      some (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 D2z)))))
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 D1z)))))
        ==(Trans.Dict.BT.D 0 D1z))=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum D2z (.D 1 (.D 1 (.D 0 D1z))))
        =[D2z,.D 1 (.D 1 (.D 0 D1z))] from rfl]
    change ((Trans.Recal.replMark (h+3) (.D 1 (.D 1 (.D 0 D1z))) (.D 0 D1z)
      (.D 0 D2z)).map (fun x=>Trans.Dict.BT.sum D2z x)).map
        (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 1 (.D 0 D1z)))==(Trans.Dict.BT.D 0 D1z))
        =false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 0 D1z))==(Trans.Dict.BT.D 0 D1z))=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change ((((Trans.Recal.replMark (h+1) (.D 0 D1z) (.D 0 D1z) (.D 0 D2z)).map
      (fun x=>Trans.Dict.BT.D 1 x)).map (fun x=>Trans.Dict.BT.D 1 x)).map
      (fun x=>Trans.Dict.BT.sum D2z x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [G1.replMark_self (h+1) 0 D1z (.D 0 D2z) (by omega)]
    rfl
  · intro n
    exact ⟨rfl,rfl,rfl⟩

theorem repl_LBT_r3 (a f : Nat) (hf : 5*a+5 ≤ f) :
    Trans.Recal.replMark f (LBT (5*a+3)) (.D 0 D2z) (.D 0 (.sum D2z D1z))
      =some (LBT (5*a+4)) := by
  rw [LBT_r a 3 (by omega),LBT_r a 4 (by omega)]
  refine repl_D0W a f 5 (Part 3) (Part 4) (.D 0 D2z) (.D 0 (.sum D2z D1z)) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
    change Trans.Recal.replMark (h+5)
      (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 D2z))))) (.D 0 D2z) (.D 0 (.sum D2z D1z))=
      some (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 (.sum D2z D1z))))))
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 D2z)))))
        ==(Trans.Dict.BT.D 0 D2z))=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum D2z (.D 1 (.D 1 (.D 0 D2z))))
        =[D2z,.D 1 (.D 1 (.D 0 D2z))] from rfl]
    change ((Trans.Recal.replMark (h+3) (.D 1 (.D 1 (.D 0 D2z))) (.D 0 D2z)
      (.D 0 (.sum D2z D1z))).map (fun x=>Trans.Dict.BT.sum D2z x)).map
        (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 1 (.D 0 D2z)))==(Trans.Dict.BT.D 0 D2z))
        =false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 0 D2z))==(Trans.Dict.BT.D 0 D2z))=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change ((((Trans.Recal.replMark (h+1) (.D 0 D2z) (.D 0 D2z)
      (.D 0 (.sum D2z D1z))).map
      (fun x=>Trans.Dict.BT.D 1 x)).map (fun x=>Trans.Dict.BT.D 1 x)).map
      (fun x=>Trans.Dict.BT.sum D2z x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [G1.replMark_self (h+1) 0 D2z (.D 0 (.sum D2z D1z)) (by omega)]
    rfl
  · intro n
    exact ⟨rfl,rfl,rfl⟩

theorem repl_LBT_r4 (a f : Nat) (hf : 5*a+7 ≤ f) :
    Trans.Recal.replMark f (LBT (5*a+4)) D1z D11z=some (LBT (5*a+5)) := by
  rw [LBT_r a 4 (by omega),show 5*a+5=5*(a+1)+0 by omega,LBT_r (a+1) 0 (by omega),
    ← W_add a 1 (Part 0)]
  refine repl_D0W a f 7 (Part 4) (W 1 (Part 0)) D1z D11z ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+7 := ⟨g-7,by omega⟩
    change Trans.Recal.replMark (h+7)
      (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 (.sum D2z D1z)))))) D1z D11z=
      some (.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 (.sum D2z (.D 1 (.D 1 .zero))))))))
    rw [show h+7=(h+6)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum D2z (.D 1 (.D 1 (.D 0 (.sum D2z D1z))))))
        ==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+6=(h+5)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum D2z (.D 1 (.D 1 (.D 0 (.sum D2z D1z)))))
        =[D2z,.D 1 (.D 1 (.D 0 (.sum D2z D1z)))] from rfl]
    change ((Trans.Recal.replMark (h+5) (.D 1 (.D 1 (.D 0 (.sum D2z D1z)))) D1z
      D11z).map (fun x=>Trans.Dict.BT.sum D2z x)).map
        (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 1 (.D 0 (.sum D2z D1z))))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 0 (.sum D2z D1z)))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum D2z D1z))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum D2z D1z)=[D2z,D1z] from rfl]
    change Option.map (fun x=>Trans.Dict.BT.D 0 x)
      (Option.map (fun x=>Trans.Dict.BT.sum D2z x)
        (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
          (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
            (Option.map (fun x=>Trans.Dict.BT.D 0 x)
              (Option.map (fun ll=>Trans.Dict.BT.ofL
                  (([D2z,D1z] : List Trans.Dict.BT).dropLast++[ll]))
                (Trans.Recal.replMark (h+1) D1z D1z D11z))))))=_
    rw [G1.replMark_self (h+1) 1 .zero D11z (by omega)]
    rfl
  · intro n
    exact ⟨rfl,rfl,rfl⟩


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
#guard rest12.any fun r => r.m==M && r.t==t && r.proof=="namespace G12"
#guard (rows.filter fun r => r.proof=="namespace G12").length==1
#guard (List.range 6).all fun n => Trans.oR (BMS.expand M n)==some (fD n)

/-! ### Link 2, step 26: the memo.

`runAux` carries a memo table, so `Trans` and `Mark` have to be proved together.
Only nine kinds of key ever enter the table: the four prefixes below `L 0`, and
`(L k, none)` / `(L k, some (markJ k))` for each `k`. -/

abbrev P1 : Trans.Recal.PS := [((0:Int),(0:Int))]
abbrev P2 : Trans.Recal.PS := [((0:Int),(0:Int)),((1:Int),(1:Int))]
abbrev P3 : Trans.Recal.PS := [((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))]
abbrev P4 : Trans.Recal.PS :=
  [((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int)),((1:Int),(1:Int))]

abbrev VP2 : Trans.Dict.BT := .D 0 D1z
abbrev VP3 : Trans.Dict.BT := .D 0 D2z
abbrev VP4 : Trans.Dict.BT := .D 0 (.sum D2z D1z)

/-- The single mark each `L k` is ever asked for. -/
def markJ (k : Nat) : Int :=
  if k%5=2 then ((k+3:Nat):Int) else if k%5=3 then ((k+2:Nat):Int) else ((k+4:Nat):Int)

/-- Its value. -/
def markV (k : Nat) : Trans.Dict.BT :=
  if k%5=1 then D0z else if k%5=2 then .D 0 D1z
  else if k%5=3 then .D 0 D2z else D1z

def Allowed (k : Nat) (req : Option Int) : Prop := req=none ∨ req=some (markJ k)

def Val (k : Nat) (req : Option Int) : Trans.Dict.BT :=
  if req=none then LBT k else markV k

theorem Allowed_none (k : Nat) : Allowed k none := Or.inl rfl
theorem Allowed_mark (k : Nat) : Allowed k (some (markJ k)) := Or.inr rfl
theorem Val_none (k : Nat) : Val k none=LBT k := by
  unfold Val; rw [if_pos rfl]
theorem Val_mark (k : Nat) : Val k (some (markJ k))=markV k := by
  unfold Val; rw [if_neg (by simp)]

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  (∀ k req, p.1=(L k,req) → Allowed k req → p.2=Val k req)
  ∧ (p.1=(P1,(none:Option Int)) → p.2=Trans.Dict.BT.zero)
  ∧ (∀ req, p.1=(P2,req) → (req=none ∨ req=some 0) → p.2=VP2)
  ∧ (∀ req, p.1=(P3,req) → (req=none ∨ req=some 0) → p.2=VP3)
  ∧ (p.1=(P4,(none:Option Int)) → p.2=VP4)
  ∧ (p.1=(P4,(some (3:Int))) → p.2=D1z)

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p∈tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun z=>z.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h),?_⟩
  have hb : p.1==key := List.find?_some (p:=fun z=>z.1==key) (a:=p) h
  exact eq_of_beq hb

/-! #### 鍵はすべて相異なる。長さで見分けられる。 -/

theorem L_inj (k k' : Nat) (h : L k=L k') : k=k' := by
  have := congrArg List.length h
  rw [length_L,length_L] at this
  omega

theorem L_ne_P1 (k : Nat) : L k≠P1 := by
  intro h
  have := congrArg List.length h
  rw [length_L] at this
  simp at this

theorem L_ne_P2 (k : Nat) : L k≠P2 := by
  intro h
  have := congrArg List.length h
  rw [length_L] at this
  simp at this

theorem L_ne_P3 (k : Nat) : L k≠P3 := by
  intro h
  have := congrArg List.length h
  rw [length_L] at this
  simp at this

theorem L_ne_P4 (k : Nat) : L k≠P4 := by
  intro h
  have := congrArg List.length h
  rw [length_L] at this
  simp at this

theorem good_L_entry (k : Nat) (req : Option Int) (hr : Allowed k req) :
    Good ((L k,req),Val k req) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro j r h _
    have hL : L k=L j := congrArg Prod.fst h
    have hkj := L_inj k j hL
    subst hkj
    have hreq : req=r := by simpa using congrArg Prod.snd h
    subst hreq
    rfl
  · intro h
    exact absurd (congrArg Prod.fst h) (L_ne_P1 k)
  · intro r h _
    exact absurd (congrArg Prod.fst h) (L_ne_P2 k)
  · intro r h _
    exact absurd (congrArg Prod.fst h) (L_ne_P3 k)
  · intro h
    exact absurd (congrArg Prod.fst h) (L_ne_P4 k)
  · intro h
    exact absurd (congrArg Prod.fst h) (L_ne_P4 k)

theorem P1_ne_P2 : (P1 : Trans.Recal.PS)≠P2 := by decide
theorem P1_ne_P3 : (P1 : Trans.Recal.PS)≠P3 := by decide
theorem P1_ne_P4 : (P1 : Trans.Recal.PS)≠P4 := by decide
theorem P2_ne_P1 : (P2 : Trans.Recal.PS)≠P1 := by decide
theorem P2_ne_P3 : (P2 : Trans.Recal.PS)≠P3 := by decide
theorem P2_ne_P4 : (P2 : Trans.Recal.PS)≠P4 := by decide
theorem P3_ne_P1 : (P3 : Trans.Recal.PS)≠P1 := by decide
theorem P3_ne_P2 : (P3 : Trans.Recal.PS)≠P2 := by decide
theorem P3_ne_P4 : (P3 : Trans.Recal.PS)≠P4 := by decide
theorem P4_ne_P1 : (P4 : Trans.Recal.PS)≠P1 := by decide
theorem P4_ne_P2 : (P4 : Trans.Recal.PS)≠P2 := by decide
theorem P4_ne_P3 : (P4 : Trans.Recal.PS)≠P3 := by decide
theorem none_ne_three : (none : Option Int)≠some 3 := by decide
theorem three_ne_none : (some (3:Int))≠(none : Option Int) := by decide

theorem good_P1_entry : Good ((P1,(none:Option Int)),Trans.Dict.BT.zero) := by
  refine ⟨?_,fun _ => rfl,?_,?_,?_,?_⟩
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (L_ne_P1 j)
  · intro r h _
    exact absurd (congrArg Prod.fst h) P1_ne_P2
  · intro r h _
    exact absurd (congrArg Prod.fst h) P1_ne_P3
  · intro h
    exact absurd (congrArg Prod.fst h) P1_ne_P4
  · intro h
    exact absurd (congrArg Prod.fst h) P1_ne_P4

theorem good_P2_entry (req : Option Int) : Good ((P2,req),VP2) := by
  refine ⟨?_,?_,fun _ _ _ => rfl,?_,?_,?_⟩
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (L_ne_P2 j)
  · intro h
    exact absurd (congrArg Prod.fst h) P2_ne_P1
  · intro r h _
    exact absurd (congrArg Prod.fst h) P2_ne_P3
  · intro h
    exact absurd (congrArg Prod.fst h) P2_ne_P4
  · intro h
    exact absurd (congrArg Prod.fst h) P2_ne_P4

theorem good_P3_entry (req : Option Int) : Good ((P3,req),VP3) := by
  refine ⟨?_,?_,?_,fun _ _ _ => rfl,?_,?_⟩
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (L_ne_P3 j)
  · intro h
    exact absurd (congrArg Prod.fst h) P3_ne_P1
  · intro r h _
    exact absurd (congrArg Prod.fst h) P3_ne_P2
  · intro h
    exact absurd (congrArg Prod.fst h) P3_ne_P4
  · intro h
    exact absurd (congrArg Prod.fst h) P3_ne_P4

theorem good_P4none_entry : Good ((P4,(none:Option Int)),VP4) := by
  refine ⟨?_,?_,?_,?_,fun _ => rfl,?_⟩
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (L_ne_P4 j)
  · intro h
    exact absurd (congrArg Prod.fst h) P4_ne_P1
  · intro r h _
    exact absurd (congrArg Prod.fst h) P4_ne_P2
  · intro r h _
    exact absurd (congrArg Prod.fst h) P4_ne_P3
  · intro h
    exact absurd (congrArg Prod.snd h) none_ne_three

theorem good_P4mark_entry : Good ((P4,(some (3:Int))),D1z) := by
  refine ⟨?_,?_,?_,?_,?_,fun _ => rfl⟩
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (L_ne_P4 j)
  · intro h
    exact absurd (congrArg Prod.fst h) P4_ne_P1
  · intro r h _
    exact absurd (congrArg Prod.fst h) P4_ne_P2
  · intro r h _
    exact absurd (congrArg Prod.fst h) P4_ne_P3
  · intro h
    exact absurd (congrArg Prod.snd h) three_ne_none

theorem Sound_cons {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT} (hp : Good p) :
    Sound (p::tbl) := by
  intro q hq
  rcases List.mem_cons.mp hq with h|h
  · subst h; exact hp
  · exact hs q h

/-! #### `L 0` の下の 4 つの前置。 -/

theorem runAux_P1 (g : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+1) P1 none).run tbl).1=Trans.Dict.BT.zero
      ∧ Sound ((Trans.Recal.runAux (g+1) P1 none).run tbl).2 := by
  cases hf : tbl.find? (fun z=>z.1==(P1,(none:Option Int))) with
  | some p =>
    rw [G1.run_hit g P1 none tbl p hf]
    obtain ⟨hg,he⟩ := good_of_find hs hf
    exact ⟨hg.2.1 he,hs⟩
  | none =>
    rw [G1.run_base g tbl hf]
    exact ⟨rfl,Sound_cons hs good_P1_entry⟩

theorem runAux_P2 (g : Nat) (req : Option Int) (hr : req=none ∨ req=some 0)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) P2 req).run tbl).1=VP2
      ∧ Sound ((Trans.Recal.runAux (g+2) P2 req).run tbl).2 := by
  cases hf : tbl.find? (fun z=>z.1==(P2,req)) with
  | some p =>
    rw [show g+2=(g+1)+1 by omega,G1.run_hit (g+1) P2 req tbl p hf]
    obtain ⟨hg,he⟩ := good_of_find hs hf
    exact ⟨hg.2.2.1 req he hr,hs⟩
  | none =>
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,
      show Trans.Recal.isReducedP P2=true from by decide,
      show Trans.Recal.isPrincipalP P2=true from by decide,
      Bool.not_true,Bool.false_eq_true,if_false,
      show Trans.Recal.lenI P2-1=(1:Int) from rfl,
      show ((1:Int)==0)=false from rfl,
      show Trans.Recal.predP P2=P1 from rfl]
    cases hrun : (Trans.Recal.runAux (g+1) P1 none) tbl with
    | mk t1 s =>
      have ih1 := runAux_P1 g tbl hs
      rw [show (Trans.Recal.runAux (g+1) P1 none).run tbl=(t1,s) from hrun] at ih1
      have ht1 : t1=Trans.Dict.BT.zero := ih1.1
      have hsm : Sound s := ih1.2
      subst ht1
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hrun,
        show ((Trans.Dict.BT.zero)==Trans.Dict.BT.zero)=true from rfl,if_true]
      rcases hr with h|h
      · subst h
        exact ⟨rfl,Sound_cons hsm (good_P2_entry none)⟩
      · subst h
        simp only [show (((0:Int))==0)=true from rfl,if_true]
        exact ⟨rfl,Sound_cons hsm (good_P2_entry (some 0))⟩


theorem runAux_P3 (g : Nat) (req : Option Int) (hr : req=none ∨ req=some 0)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+3) P3 req).run tbl).1=VP3
      ∧ Sound ((Trans.Recal.runAux (g+3) P3 req).run tbl).2 := by
  cases hf : tbl.find? (fun z=>z.1==(P3,req)) with
  | some p =>
    rw [show g+3=(g+2)+1 by omega,G1.run_hit (g+2) P3 req tbl p hf]
    obtain ⟨hg,he⟩ := good_of_find hs hf
    exact ⟨hg.2.2.2.1 req he hr,hs⟩
  | none =>
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,
      show Trans.Recal.isReducedP P3=true from by decide,
      show Trans.Recal.isPrincipalP P3=true from by decide,
      Bool.not_true,Bool.false_eq_true,if_false,
      show Trans.Recal.lenI P3-1=(2:Int) from rfl,
      show ((2:Int)==0)=false from rfl,
      show Trans.Recal.predP P3=P2 from rfl]
    cases hrun : (Trans.Recal.runAux (g+2) P2 none) tbl with
    | mk t1 s =>
      have ih1 := runAux_P2 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+2) P2 none).run tbl=(t1,s) from hrun] at ih1
      have ht1 : t1=VP2 := ih1.1
      have hsm : Sound s := ih1.2
      subst ht1
      cases hrun2 : (Trans.Recal.runAux (g+2) P2 (some 0)) s with
      | mk c1 s2 =>
        have ih2 := runAux_P2 g (some 0) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+2) P2 (some 0)).run s=(c1,s2) from hrun2] at ih2
        have hc1 : c1=VP2 := ih2.1
        have hsm2 : Sound s2 := ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,hrun2,
          show ((VP2)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar P3 0 2 0=1 from by decide,
          show Trans.Recal.adm P3 1=0 from by decide,
          show Trans.Recal.transTypeMain P3 1 2=6 from by decide,
          show Trans.Recal.mkC2 P3 1 2 6 VP2=VP3 from by decide]
        rcases hr with h|h
        · subst h
          refine ⟨?_,Sound_cons hsm2 (good_P3_entry none)⟩
          show (Trans.Recal.replMark
            (Trans.Dict.BT.size VP2+(Trans.Dict.BT.size VP2
              +Trans.Dict.BT.size VP3+4)) VP2 VP2 VP3).getD Trans.Dict.BT.zero=VP3
          rfl
        · subst h
          cases hrun3 : (Trans.Recal.runAux (g+2) P2 (some 0)) s2 with
          | mk c0 s3 =>
            have ih3 := runAux_P2 g (some 0) (Or.inr rfl) s2 hsm2
            rw [show (Trans.Recal.runAux (g+2) P2 (some 0)).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0 : c0=VP2 := ih3.1
            have hsm3 : Sound s3 := ih3.2
            subst hc0
            simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            rw [if_pos (show (0:Int)<2 by omega)]
            simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run,hrun3,
              show Trans.Recal.isMarkedB VP2 VP2=true from by decide,if_true]
            exact ⟨rfl,Sound_cons hsm3 (good_P3_entry (some 0))⟩


def ValP4 (req : Option Int) : Trans.Dict.BT := if req=none then VP4 else D1z

theorem ValP4_none : ValP4 none=VP4 := by unfold ValP4; rw [if_pos rfl]
theorem ValP4_mark : ValP4 (some 3)=D1z := by unfold ValP4; rw [if_neg (by simp)]

theorem good_P4_entry (req : Option Int) (hr : req=none ∨ req=some 3) :
    Good ((P4,req),ValP4 req) := by
  rcases hr with h|h <;> subst h
  · rw [ValP4_none]; exact good_P4none_entry
  · rw [ValP4_mark]; exact good_P4mark_entry

theorem runAux_P4 (g : Nat) (req : Option Int) (hr : req=none ∨ req=some 3)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+4) P4 req).run tbl).1=ValP4 req
      ∧ Sound ((Trans.Recal.runAux (g+4) P4 req).run tbl).2 := by
  cases hf : tbl.find? (fun z=>z.1==(P4,req)) with
  | some p =>
    rw [show g+4=(g+3)+1 by omega,G1.run_hit (g+3) P4 req tbl p hf]
    obtain ⟨hg,he⟩ := good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h <;> subst h
    · rw [ValP4_none]; exact hg.2.2.2.2.1 he
    · rw [ValP4_mark]; exact hg.2.2.2.2.2 he
  | none =>
    rw [show g+4=(g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,
      show Trans.Recal.isReducedP P4=true from by decide,
      show Trans.Recal.isPrincipalP P4=true from by decide,
      Bool.not_true,Bool.false_eq_true,if_false,
      show Trans.Recal.lenI P4-1=(3:Int) from rfl,
      show ((3:Int)==0)=false from rfl,
      show Trans.Recal.predP P4=P3 from rfl]
    cases hrun : (Trans.Recal.runAux (g+3) P3 none) tbl with
    | mk t1 s =>
      have ih1 := runAux_P3 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+3) P3 none).run tbl=(t1,s) from hrun] at ih1
      have ht1 : t1=VP3 := ih1.1
      have hsm : Sound s := ih1.2
      subst ht1
      cases hrun2 : (Trans.Recal.runAux (g+3) P3 (some 0)) s with
      | mk c1 s2 =>
        have ih2 := runAux_P3 g (some 0) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+3) P3 (some 0)).run s=(c1,s2) from hrun2] at ih2
        have hc1 : c1=VP3 := ih2.1
        have hsm2 : Sound s2 := ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,hrun2,
          show ((VP3)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar P4 0 3 0=0 from by decide,
          show Trans.Recal.adm P4 0=0 from by decide,
          show Trans.Recal.transTypeMain P4 0 3=5 from by decide,
          show Trans.Recal.mkC2 P4 0 3 5 VP3=VP4 from by decide]
        rcases hr with h|h
        · subst h
          rw [ValP4_none]
          exact ⟨rfl,Sound_cons hsm2 good_P4none_entry⟩
        · subst h
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          rw [if_neg (show ¬((3:Int)<3) by omega),ValP4_mark]
          exact ⟨rfl,Sound_cons hsm2 good_P4mark_entry⟩


/-! #### 一段の型。5 相のうち 3 相は印が末尾に、2 相は 1 つ内側にある。 -/

theorem LBT_ne_zero (m : Nat) : ((LBT m)==Trans.Dict.BT.zero)=false := by
  unfold LBT
  rfl

theorem size_W (n : Nat) (b : Trans.Dict.BT) : (W n b).size=6*n+b.size := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    show (Trans.Dict.BT.sum D2z (.D 1 (.D 1 (.D 0 (W n b))))).size=_
    simp only [Trans.Dict.BT.size,ih]
    omega

theorem size_LBT_ge (m : Nat) : 6*(m/5)+1 ≤ (LBT m).size := by
  unfold LBT
  show 6*(m/5)+1 ≤ 1+(W (m/5) (Part (m%5))).size
  rw [size_W]
  have : 1 ≤ (Part (m%5)).size := by
    unfold Part
    split <;> simp [Trans.Dict.BT.size]
  omega

theorem lenI_L_succ (k : Nat) : Trans.Recal.lenI (L (k+1))-1=((((k+1)+4:Nat)):Int) := by
  rw [lenI_L]
  omega

theorem runAux_step_top (k g : Nat) (j0 : Int) (ty : Nat) (c2 : Trans.Dict.BT)
    (req : Option Int) (hr : Allowed (k+1) req)
    (hj0 : Trans.Recal.fpar (L (k+1)) 0 ((((k+1)+4:Nat)):Int) 0=j0)
    (hty : Trans.Recal.transTypeMain (L (k+1)) j0 ((((k+1)+4:Nat)):Int)=ty)
    (hadm : Trans.Recal.adm (L (k+1)) j0=markJ k)
    (hc2 : Trans.Recal.mkC2 (L (k+1)) j0 ((((k+1)+4:Nat)):Int) ty (markV k)=c2)
    (hnone : (Trans.Recal.replMark
        (Trans.Dict.BT.size (LBT k)
          +(Trans.Dict.BT.size (markV k)+Trans.Dict.BT.size c2+4))
        (LBT k) (markV k) c2).getD Trans.Dict.BT.zero=LBT (k+1))
    (htop : markJ (k+1)=((((k+1)+4:Nat)):Int))
    (hmv : Trans.Dict.BT.D (Trans.Recal.gp1 (L (k+1)) ((((k+1)+4:Nat)):Int)).toNat
      Trans.Dict.BT.zero=markV (k+1))
    (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r, Allowed k r → ∀ s, Sound s →
      ((Trans.Recal.runAux (k+g+6) (L k) r).run s).1=Val k r
        ∧ Sound ((Trans.Recal.runAux (k+g+6) (L k) r).run s).2) :
    ((Trans.Recal.runAux ((k+1)+g+6) (L (k+1)) req).run tbl).1=Val (k+1) req
      ∧ Sound ((Trans.Recal.runAux ((k+1)+g+6) (L (k+1)) req).run tbl).2 := by
  cases hf : tbl.find? (fun z=>z.1==(L (k+1),req)) with
  | some p =>
    rw [show (k+1)+g+6=(k+g+6)+1 by omega,
      G1.run_hit (k+g+6) (L (k+1)) req tbl p hf]
    obtain ⟨hg,he⟩ := good_of_find hs hf
    exact ⟨hg.1 (k+1) req he hr,hs⟩
  | none =>
    rw [show (k+1)+g+6=(k+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,
      isReducedP_L (k+1),isPrincipalP_L (k+1),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L_succ k,
      show (((((k+1)+4:Nat)):Int)==0)=false from beq_eq_false_iff_ne.mpr (by omega),
      predP_L k]
    cases hrun : (Trans.Recal.runAux (k+g+6) (L k) none) tbl with
    | mk t1 s =>
      have ih1 := ih none (Allowed_none k) tbl hs
      rw [show (Trans.Recal.runAux (k+g+6) (L k) none).run tbl=(t1,s) from hrun] at ih1
      have ht1 : t1=LBT k := by simpa only [Val_none] using ih1.1
      have hsm : Sound s := ih1.2
      subst ht1
      cases hrun2 : (Trans.Recal.runAux (k+g+6) (L k) (some (markJ k))) s with
      | mk c1 s2 =>
        have ih2 := ih (some (markJ k)) (Allowed_mark k) s hsm
        rw [show (Trans.Recal.runAux (k+g+6) (L k) (some (markJ k))).run s=(c1,s2)
          from hrun2] at ih2
        have hc1 : c1=markV k := by simpa only [Val_mark] using ih2.1
        have hsm2 : Sound s2 := ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,hrun2,LBT_ne_zero k,
          Bool.false_eq_true,if_false,hj0,hty,hadm,hc2]
        rcases hr with h|h
        · subst h
          rw [Val_none,hnone]
          have hgood : Good ((L (k+1),(none:Option Int)),Val (k+1) none) :=
            good_L_entry (k+1) none (Allowed_none (k+1))
          rw [Val_none] at hgood
          exact ⟨rfl,Sound_cons hsm2 hgood⟩
        · subst h
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          rw [htop,if_neg (show ¬(((((k+1)+4:Nat)):Int)<((((k+1)+4:Nat)):Int)) by omega),
            hmv,← htop,Val_mark]
          exact ⟨rfl,Sound_cons hsm2 (by
            have hgood : Good ((L (k+1),some (markJ (k+1))),Val (k+1)
              (some (markJ (k+1)))) := good_L_entry (k+1) _ (Allowed_mark (k+1))
            rwa [Val_mark] at hgood)⟩


theorem isMarkedB_self (t : Trans.Dict.BT) : Trans.Recal.isMarkedB t t=true := by
  unfold Trans.Recal.isMarkedB
  obtain ⟨u,hu⟩ : ∃ u, Trans.Dict.BT.size t+2=u+1 := ⟨Trans.Dict.BT.size t+1,by omega⟩
  rw [hu]
  show (if t==t then true else _)=true
  rw [if_pos (G1.beq_BT_self t)]

theorem runAux_step_inner (k g : Nat) (j0 : Int) (ty : Nat) (c2 : Trans.Dict.BT)
    (req : Option Int) (hr : Allowed (k+1) req)
    (hj0 : Trans.Recal.fpar (L (k+1)) 0 ((((k+1)+4:Nat)):Int) 0=j0)
    (hty : Trans.Recal.transTypeMain (L (k+1)) j0 ((((k+1)+4:Nat)):Int)=ty)
    (hadm : Trans.Recal.adm (L (k+1)) j0=markJ k)
    (hc2 : Trans.Recal.mkC2 (L (k+1)) j0 ((((k+1)+4:Nat)):Int) ty (markV k)=c2)
    (hnone : (Trans.Recal.replMark
        (Trans.Dict.BT.size (LBT k)
          +(Trans.Dict.BT.size (markV k)+Trans.Dict.BT.size c2+4))
        (LBT k) (markV k) c2).getD Trans.Dict.BT.zero=LBT (k+1))
    (hin : markJ (k+1)=markJ k) (hlt : markJ (k+1)<((((k+1)+4:Nat)):Int))
    (hreplm : (Trans.Recal.replMark
        (Trans.Dict.BT.size (markV k)
          +(Trans.Dict.BT.size (markV k)+Trans.Dict.BT.size c2+4))
        (markV k) (markV k) c2).getD Trans.Dict.BT.zero=markV (k+1))
    (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r, Allowed k r → ∀ s, Sound s →
      ((Trans.Recal.runAux (k+g+6) (L k) r).run s).1=Val k r
        ∧ Sound ((Trans.Recal.runAux (k+g+6) (L k) r).run s).2) :
    ((Trans.Recal.runAux ((k+1)+g+6) (L (k+1)) req).run tbl).1=Val (k+1) req
      ∧ Sound ((Trans.Recal.runAux ((k+1)+g+6) (L (k+1)) req).run tbl).2 := by
  cases hf : tbl.find? (fun z=>z.1==(L (k+1),req)) with
  | some p =>
    rw [show (k+1)+g+6=(k+g+6)+1 by omega,
      G1.run_hit (k+g+6) (L (k+1)) req tbl p hf]
    obtain ⟨hg,he⟩ := good_of_find hs hf
    exact ⟨hg.1 (k+1) req he hr,hs⟩
  | none =>
    rw [show (k+1)+g+6=(k+g+6)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,
      isReducedP_L (k+1),isPrincipalP_L (k+1),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L_succ k,
      show (((((k+1)+4:Nat)):Int)==0)=false from beq_eq_false_iff_ne.mpr (by omega),
      predP_L k]
    cases hrun : (Trans.Recal.runAux (k+g+6) (L k) none) tbl with
    | mk t1 s =>
      have ih1 := ih none (Allowed_none k) tbl hs
      rw [show (Trans.Recal.runAux (k+g+6) (L k) none).run tbl=(t1,s) from hrun] at ih1
      have ht1 : t1=LBT k := by simpa only [Val_none] using ih1.1
      have hsm : Sound s := ih1.2
      subst ht1
      cases hrun2 : (Trans.Recal.runAux (k+g+6) (L k) (some (markJ k))) s with
      | mk c1 s2 =>
        have ih2 := ih (some (markJ k)) (Allowed_mark k) s hsm
        rw [show (Trans.Recal.runAux (k+g+6) (L k) (some (markJ k))).run s=(c1,s2)
          from hrun2] at ih2
        have hc1 : c1=markV k := by simpa only [Val_mark] using ih2.1
        have hsm2 : Sound s2 := ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,hrun2,LBT_ne_zero k,
          Bool.false_eq_true,if_false,hj0,hty,hadm,hc2]
        rcases hr with h|h
        · subst h
          rw [Val_none,hnone]
          have hgood : Good ((L (k+1),(none:Option Int)),Val (k+1) none) :=
            good_L_entry (k+1) none (Allowed_none (k+1))
          rw [Val_none] at hgood
          exact ⟨rfl,Sound_cons hsm2 hgood⟩
        · subst h
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          rw [if_pos hlt,hin]
          cases hrun3 : (Trans.Recal.runAux (k+g+6) (L k) (some (markJ k))) s2 with
          | mk c0 s3 =>
            have ih3 := ih (some (markJ k)) (Allowed_mark k) s2 hsm2
            rw [show (Trans.Recal.runAux (k+g+6) (L k) (some (markJ k))).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0 : c0=markV k := by simpa only [Val_mark] using ih3.1
            have hsm3 : Sound s3 := ih3.2
            subst hc0
            simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run,hrun3,isMarkedB_self (markV k),if_true]
            rw [hreplm,← hin,Val_mark]
            have hgood : Good ((L (k+1),some (markJ (k+1))),Val (k+1)
              (some (markJ (k+1)))) := good_L_entry (k+1) _ (Allowed_mark (k+1))
            rw [Val_mark] at hgood
            exact ⟨rfl,Sound_cons hsm3 hgood⟩


theorem size_pos (t : Trans.Dict.BT) : 1 ≤ t.size := by
  cases t <;> simp [Trans.Dict.BT.size] <;> omega

theorem markJ_top (k : Nat) (h : ¬(k%5=2 ∨ k%5=3)) : markJ k=(((k+4:Nat)):Int) := by
  unfold markJ
  rw [if_neg (by omega),if_neg (by omega)]

theorem markJ_r2 (k : Nat) (h : k%5=2) : markJ k=(((k+3:Nat)):Int) := by
  unfold markJ; rw [if_pos h]

theorem markJ_r3 (k : Nat) (h : k%5=3) : markJ k=(((k+2:Nat)):Int) := by
  unfold markJ; rw [if_neg (by omega),if_pos h]

theorem markV_r0 (k : Nat) (h : k%5=0) : markV k=D1z := by
  unfold markV; rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
theorem markV_r1 (k : Nat) (h : k%5=1) : markV k=D0z := by
  unfold markV; rw [if_pos h]
theorem markV_r2 (k : Nat) (h : k%5=2) : markV k=.D 0 D1z := by
  unfold markV; rw [if_neg (by omega),if_pos h]
theorem markV_r3 (k : Nat) (h : k%5=3) : markV k=.D 0 D2z := by
  unfold markV; rw [if_neg (by omega),if_neg (by omega),if_pos h]
theorem markV_r4 (k : Nat) (h : k%5=4) : markV k=D1z := by
  unfold markV; rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

theorem runAux_L0 (g : Nat) (req : Option Int) (hr : Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (0+g+6) (L 0) req).run tbl).1=Val 0 req
      ∧ Sound ((Trans.Recal.runAux (0+g+6) (L 0) req).run tbl).2 := by
  cases hf : tbl.find? (fun z=>z.1==(L 0,req)) with
  | some p =>
    rw [show 0+g+6=(g+5)+1 by omega,G1.run_hit (g+5) (L 0) req tbl p hf]
    obtain ⟨hg,he⟩ := good_of_find hs hf
    exact ⟨hg.1 0 req he hr,hs⟩
  | none =>
    rw [show 0+g+6=(g+5)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,
      isReducedP_L 0,isPrincipalP_L 0,
      Bool.not_true,Bool.false_eq_true,if_false,
      show Trans.Recal.lenI (L 0)-1=(4:Int) from by rw [lenI_L]; omega,
      show ((4:Int)==0)=false from rfl,
      show Trans.Recal.predP (L 0)=P4 from rfl]
    cases hrun : (Trans.Recal.runAux (g+5) P4 none) tbl with
    | mk t1 s =>
      have ih1 := runAux_P4 (g+1) none (Or.inl rfl) tbl hs
      rw [show g+1+4=g+5 by omega] at ih1
      rw [show (Trans.Recal.runAux (g+5) P4 none).run tbl=(t1,s) from hrun] at ih1
      have ht1 : t1=VP4 := by rw [← ValP4_none]; exact ih1.1
      have hsm : Sound s := ih1.2
      subst ht1
      cases hrun2 : (Trans.Recal.runAux (g+5) P4 (some 3)) s with
      | mk c1 s2 =>
        have ih2 := runAux_P4 (g+1) (some 3) (Or.inr rfl) s hsm
        rw [show g+1+4=g+5 by omega] at ih2
        rw [show (Trans.Recal.runAux (g+5) P4 (some 3)).run s=(c1,s2) from hrun2] at ih2
        have hc1 : c1=D1z := by rw [← ValP4_mark]; exact ih2.1
        have hsm2 : Sound s2 := ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,hrun2,
          show ((VP4)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (L 0) 0 4 0=3 from by
            have := j0_L_not4 0 (by omega)
            simpa using this,
          show Trans.Recal.adm (L 0) 3=3 from by
            have := adm_L_r0 0 (by omega)
            simpa using this,
          show Trans.Recal.transTypeMain (L 0) 3 4=3 from by
            have := transType_L_r0 0 (by omega)
            simpa using this,
          show Trans.Recal.mkC2 (L 0) 3 4 3 D1z=D11z from by
            have := mkC2_L_r0 0 (by omega)
            simpa using this]
        rcases hr with h|h
        · subst h
          rw [Val_none,
            show (Trans.Recal.replMark
              (Trans.Dict.BT.size VP4+(Trans.Dict.BT.size D1z
                +Trans.Dict.BT.size D11z+4)) VP4 D1z D11z).getD Trans.Dict.BT.zero
              =LBT 0 from by decide]
          have hgood : Good ((L 0,(none:Option Int)),Val 0 none) :=
            good_L_entry 0 none (Allowed_none 0)
          rw [Val_none] at hgood
          exact ⟨rfl,Sound_cons hsm2 hgood⟩
        · subst h
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          rw [show markJ 0=(4:Int) from by unfold markJ; decide,
            if_neg (show ¬((4:Int)<4) by omega),
            show Trans.Dict.BT.D (Trans.Recal.gp1 (L 0) 4).toNat Trans.Dict.BT.zero
              =Val 0 (some (markJ 0)) from by
              rw [Val_mark,markV_r0 0 (by omega)]
              rfl]
          have hgood : Good ((L 0,some (markJ 0)),Val 0 (some (markJ 0))) :=
            good_L_entry 0 _ (Allowed_mark 0)
          rw [show markJ 0=(4:Int) from by unfold markJ; decide] at hgood
          exact ⟨rfl,Sound_cons hsm2 hgood⟩


/-! #### 5 相を回して、梯子の全長で帰納する。 -/

theorem runAux_L : ∀ (k g : Nat) (req : Option Int), Allowed k req →
    ∀ tbl : Trans.Recal.Memo, Sound tbl →
      ((Trans.Recal.runAux (k+g+6) (L k) req).run tbl).1=Val k req
        ∧ Sound ((Trans.Recal.runAux (k+g+6) (L k) req).run tbl).2
  | 0,g,req,hr,tbl,hs => runAux_L0 g req hr tbl hs
  | k+1,g,req,hr,tbl,hs => by
    have ih : ∀ r, Allowed k r → ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux (k+g+6) (L k) r).run s).1=Val k r
          ∧ Sound ((Trans.Recal.runAux (k+g+6) (L k) r).run s).2 :=
      fun r hrr s hss => runAux_L k g r hrr s hss
    rcases (show (k+1)%5=0 ∨ (k+1)%5=1 ∨ (k+1)%5=2 ∨ (k+1)%5=3 ∨ (k+1)%5=4
      by omega) with h|h|h|h|h
    · refine runAux_step_top k g ((((k+1)+3:Nat)):Int) 3 D11z req hr
        (j0_L_not4 (k+1) (by omega)) (transType_L_r0 (k+1) (by omega))
        (by rw [adm_L_r0 (k+1) (by omega),markJ_top k (by omega)]; try omega)
        (by rw [markV_r4 k (by omega)]; exact mkC2_L_r0 (k+1) (by omega))
        ?_ (by rw [markJ_top (k+1) (by omega)])
        (by rw [gp1_L (k+1) ((k+1)+4) (by omega),Gq_r4 ((k+1)+4) (by omega),
              markV_r0 (k+1) (by omega)]
            rfl) tbl hs ih
      rw [markV_r4 k (by omega)]
      obtain ⟨a,rfl⟩ : ∃ a, k=5*a+4 := ⟨k/5,by omega⟩
      rw [show 5*a+4+1=5*a+5 by omega,repl_LBT_r4 a _ (by
        have hz := size_LBT_ge (5*a+4)
        rw [show (5*a+4)/5=a by omega] at hz
        have e1 : Trans.Dict.BT.size D1z=2 := rfl
        have e2 : Trans.Dict.BT.size D11z=3 := rfl
        omega)]
      rfl
    · refine runAux_step_top k g ((((k+1)+3:Nat)):Int) 1 (.D 1 D0z) req hr
        (j0_L_not4 (k+1) (by omega)) (transType_L_r1 (k+1) (by omega))
        (by rw [adm_L_r1 (k+1) (by omega),markJ_top k (by omega)]; try omega)
        (by rw [markV_r0 k (by omega)]; exact mkC2_L_r1 (k+1) (by omega))
        ?_ (by rw [markJ_top (k+1) (by omega)])
        (by rw [gp1_L (k+1) ((k+1)+4) (by omega),Gq_r0 ((k+1)+4) (by omega),
              markV_r1 (k+1) (by omega)]
            rfl) tbl hs ih
      rw [markV_r0 k (by omega)]
      obtain ⟨a,rfl⟩ : ∃ a, k=5*a := ⟨k/5,by omega⟩
      rw [show 5*a+1=5*a+1 from rfl,repl_LBT_r0 a _ (by
        have hz := size_LBT_ge (5*a)
        rw [show (5*a)/5=a by omega] at hz
        have e1 : Trans.Dict.BT.size D1z=2 := rfl
        have e2 : Trans.Dict.BT.size (Trans.Dict.BT.D 1 D0z)=3 := rfl
        omega)]
      rfl
    · refine runAux_step_inner k g ((((k+1)+3:Nat)):Int) 6 (.D 0 D1z) req hr
        (j0_L_not4 (k+1) (by omega)) (transType_L_r2 (k+1) (by omega))
        (by rw [adm_L_r2 (k+1) (by omega),markJ_top k (by omega)]; try omega)
        (by rw [markV_r1 k (by omega)]; exact mkC2_L_r2 (k+1) (by omega))
        ?_ (by rw [markJ_r2 (k+1) (by omega),markJ_top k (by omega)]; try omega)
        (by rw [markJ_r2 (k+1) (by omega)]; try omega)
        (by rw [markV_r1 k (by omega),markV_r2 (k+1) (by omega)]; decide)
        tbl hs ih
      rw [markV_r1 k (by omega)]
      obtain ⟨a,rfl⟩ : ∃ a, k=5*a+1 := ⟨k/5,by omega⟩
      rw [show 5*a+1+1=5*a+2 by omega,repl_LBT_r1 a _ (by
        have hz := size_LBT_ge (5*a+1)
        rw [show (5*a+1)/5=a by omega] at hz
        have e1 : Trans.Dict.BT.size D0z=2 := rfl
        have e2 : Trans.Dict.BT.size (Trans.Dict.BT.D 0 D1z)=3 := rfl
        omega)]
      rfl
    · refine runAux_step_inner k g ((((k+1)+3:Nat)):Int) 6 (.D 0 D2z) req hr
        (j0_L_not4 (k+1) (by omega)) (transType_L_r3 (k+1) (by omega))
        (by rw [adm_L_r3 (k+1) (by omega),markJ_r2 k (by omega)]; try omega)
        (by rw [markV_r2 k (by omega)]; exact mkC2_L_r3 (k+1) (by omega))
        ?_ (by rw [markJ_r3 (k+1) (by omega),markJ_r2 k (by omega)]; try omega)
        (by rw [markJ_r3 (k+1) (by omega)]; try omega)
        (by rw [markV_r2 k (by omega),markV_r3 (k+1) (by omega)]; decide)
        tbl hs ih
      rw [markV_r2 k (by omega)]
      obtain ⟨a,rfl⟩ : ∃ a, k=5*a+2 := ⟨k/5,by omega⟩
      rw [show 5*a+2+1=5*a+3 by omega,repl_LBT_r2 a _ (by
        have hz := size_LBT_ge (5*a+2)
        rw [show (5*a+2)/5=a by omega] at hz
        have e1 : Trans.Dict.BT.size (Trans.Dict.BT.D 0 D1z)=3 := rfl
        have e2 : Trans.Dict.BT.size (Trans.Dict.BT.D 0 D2z)=3 := rfl
        omega)]
      rfl
    · refine runAux_step_top k g ((((k+1)+1:Nat)):Int) 5 (.D 0 (.sum D2z D1z)) req hr
        (j0_L_four (k+1) (by omega)) (transType_L_r4 (k+1) (by omega))
        (by rw [adm_L_r4 (k+1) (by omega),markJ_r3 k (by omega)]; try omega)
        (by rw [markV_r3 k (by omega)]; exact mkC2_L_r4 (k+1) (by omega))
        ?_ (by rw [markJ_top (k+1) (by omega)])
        (by rw [gp1_L (k+1) ((k+1)+4) (by omega),Gq_r3 ((k+1)+4) (by omega),
              markV_r4 (k+1) (by omega)]
            rfl) tbl hs ih
      rw [markV_r3 k (by omega)]
      obtain ⟨a,rfl⟩ : ∃ a, k=5*a+3 := ⟨k/5,by omega⟩
      rw [show 5*a+3+1=5*a+4 by omega,repl_LBT_r3 a _ (by
        have hz := size_LBT_ge (5*a+3)
        rw [show (5*a+3)/5=a by omega] at hz
        have e1 : Trans.Dict.BT.size (Trans.Dict.BT.D 0 D2z)=3 := rfl
        have e2 : Trans.Dict.BT.size (Trans.Dict.BT.D 0 (.sum D2z D1z))=6 := rfl
        omega)]
      rfl


/-- **リンク 2。** 読み手は梯子を最後まで追う。 -/
theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m)=LBT m := by
  have hb : m+6 ≤ Trans.Recal.transFuel (L m) := by
    show m+6 ≤ 40+6*((L m).length+Trans.Recal.maxE (L m))
    rw [length_L]
    omega
  have h : Trans.Recal.transFuel (L m)=m+(Trans.Recal.transFuel (L m)-m-6)+6 := by
    omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L m)) (L m) none).run []).1=_
  rw [h]
  simpa only [Val_none] using (runAux_L m _ none (Allowed_none m) [] Sound_nil).1


/-! ### 行が閉じる。 -/

theorem one_lt_fD (n : Nat) : lt TM.Term.one (fD n)=true :=
  Evidence.WF.lt_trans_inT (by decide) Cps_inT (fD_inT n) (by decide) (Cps_lt_fD n)

theorem le_fD_one (n : Nat) : le (fD n) TM.Term.one=false := by
  unfold le
  rw [fD_bne_one n]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (by decide) (fD_inT n) (one_lt_fD n)

theorem one_plus_fD (n : Nat) : plus TM.Term.one (fD n)=fD n := by
  unfold plus
  rw [show TM.Term.one.toList=[TM.Term.one] from rfl,fD_toList]
  simp only [List.filter_cons,List.filter_nil,le_fD_one,Bool.false_eq_true,
    if_false,List.nil_append,TM.Term.ofList]

/-- **Γ_{ψ₀(Ω₂)+1} の行が `oR` の側で全 n について定理になった。** -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fD n) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map
          Trans.Recal.transPort).map
            (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=some (fD n)
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_L,dict_LBT,one_plus_fD]


#print axioms ofMatrix_M
#print axioms transPort_L
#print axioms oR_M

end G12
end Rows.Selected
