import Rows.G10

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
