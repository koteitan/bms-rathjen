import Trans.Recal

open Trans

namespace Rows.Ladder

/-! # 梯子の一般補題

`red` の第 1 分岐が要求するのは、行 0 の親の鎖が 0 まで降りることだけである。
その 1 点から `isAnc`・`isPrincipalP`・`ppair` が出る。行ごとに書き直さない。 -/

theorem isAncAux_step (M : Trans.Recal.PS) (f i : Nat) (j0 kk : Int) :
    Trans.Recal.isAncAux (f+1) M i j0 kk
      = if kk==j0 then true
        else if Trans.Recal.fpar M i j0 kk==-1 then false
             else Trans.Recal.isAncAux f M i (Trans.Recal.fpar M i j0 kk) kk := rfl

theorem fAncAux_step (M : Trans.Recal.PS) (f i : Nat) (j0 kk : Int) (acc : List Int) :
    Trans.Recal.fAncAux (f+1) M i j0 kk acc
      = if Trans.Recal.fpar M i j0 0 ≥ kk then
          Trans.Recal.fAncAux f M i (Trans.Recal.fpar M i j0 0) kk
            (acc++[Trans.Recal.fpar M i j0 0])
        else acc := rfl

theorem ppairAux_step (M : Trans.Recal.PS) (f : Nat) (j1 : Int)
    (acc : List Trans.Recal.PS) :
    Trans.Recal.ppairAux (f+1) M j1 acc
      = if j1<0 then acc
        else Trans.Recal.ppairAux f M
          (((Trans.Recal.fAnc M 0 j1 0).getLast?).getD 0-1)
          (Trans.Recal.slice M (((Trans.Recal.fAnc M 0 j1 0).getLast?).getD 0) (j1+1)
            :: acc) := rfl

variable {M : Trans.Recal.PS} {par : Nat → Nat}

/-- 行 0 の親が「0 で止まり、それ以外は狭義に減る」なら、どの添字も 0 の子孫。 -/
theorem isAncAux_of_chain
    (hpar : ∀ k, 1 ≤ k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int))
    (hlt : ∀ k, 1 ≤ k → k<M.length → par k<k)
    (hzero : Trans.Recal.fpar M 0 ((0:Nat):Int) 0=-1) :
    ∀ (f k : Nat), k<M.length → k<f →
      Trans.Recal.isAncAux f M 0 ((k:Nat):Int) 0=true := by
  intro f
  induction f with
  | zero => intro k _ h; exact absurd h (by omega)
  | succ f ih =>
    intro k hk hkf
    rw [isAncAux_step]
    by_cases h0 : k=0
    · subst h0
      rw [if_pos (by rfl)]
    · rw [if_neg (by
        intro hc
        have : ((0:Int))=((k:Nat):Int) := by simpa using hc
        omega)]
      rw [hpar k (by omega) hk]
      rw [if_neg (by
        intro hc
        have : ((par k : Nat) : Int)=-1 := by simpa using hc
        omega)]
      exact ih (par k) (by have := hlt k (by omega) hk; omega)
        (by have := hlt k (by omega) hk; omega)

theorem isAnc_of_chain
    (hpar : ∀ k, 1 ≤ k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int))
    (hlt : ∀ k, 1 ≤ k → k<M.length → par k<k)
    (hzero : Trans.Recal.fpar M 0 ((0:Nat):Int) 0=-1) (hlen : 1 ≤ M.length) :
    Trans.Recal.isAnc M 0 (Trans.Recal.lenI M-1) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  rw [show Trans.Recal.lenI M-1=(((M.length-1:Nat)):Int) from by
    unfold Trans.Recal.lenI; omega]
  exact isAncAux_of_chain hpar hlt hzero (M.length+1) (M.length-1) (by omega) (by omega)

theorem isPrincipalP_of_chain
    (hpar : ∀ k, 1 ≤ k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int))
    (hlt : ∀ k, 1 ≤ k → k<M.length → par k<k)
    (hzero : Trans.Recal.fpar M 0 ((0:Nat):Int) 0=-1) (hlen : 2 ≤ M.length) :
    Trans.Recal.isPrincipalP M=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP M=false from by
    unfold Trans.Recal.isZeroP
    rw [show (M.length==1)=false from by simp; omega]
    rfl]
  rw [isAnc_of_chain hpar hlt hzero (by omega)]
  rfl

theorem fAncAux_of_chain
    (hpar : ∀ k, 1 ≤ k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int))
    (hlt : ∀ k, 1 ≤ k → k<M.length → par k<k)
    (hzero : Trans.Recal.fpar M 0 ((0:Nat):Int) 0=-1) :
    ∀ (f k : Nat) (acc : List Int), k<M.length → k<f →
      (Trans.Recal.fAncAux f M 0 ((k:Nat):Int) 0 (acc++[((k:Nat):Int)])).getLast?
        = some 0 := by
  intro f
  induction f with
  | zero => intro k _ _ h; exact absurd h (by omega)
  | succ f ih =>
    intro k acc hk hkf
    rw [fAncAux_step]
    by_cases h0 : k=0
    · subst h0
      rw [hzero,if_neg (by omega)]
      simp
    · rw [hpar k (by omega) hk,if_pos (by omega)]
      have := ih (par k) (acc++[((k:Nat):Int)])
        (by have := hlt k (by omega) hk; omega)
        (by have := hlt k (by omega) hk; omega)
      simpa only [List.append_assoc] using this

theorem slice_full (M : Trans.Recal.PS) :
    Trans.Recal.slice M 0 (((M.length:Nat)):Int)=M := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show ((((M.length:Nat)):Int)-0).toNat=M.length from by omega]
  rw [List.take_of_length_le (by omega)]

/-- **梯子は 1 つの主要ブロック。** -/
theorem ppair_of_chain
    (hpar : ∀ k, 1 ≤ k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int))
    (hlt : ∀ k, 1 ≤ k → k<M.length → par k<k)
    (hzero : Trans.Recal.fpar M 0 ((0:Nat):Int) 0=-1) (hlen : 1 ≤ M.length) :
    Trans.Recal.ppair M=[M] := by
  unfold Trans.Recal.ppair
  rw [show Trans.Recal.lenI M-1=(((M.length-1:Nat)):Int) from by
    unfold Trans.Recal.lenI; omega]
  rw [show M.length+1=(M.length)+1 from rfl,ppairAux_step,if_neg (by omega)]
  rw [show Trans.Recal.fAnc M 0 (((M.length-1:Nat)):Int) 0
      = Trans.Recal.fAncAux (M.length+1) M 0 (((M.length-1:Nat)):Int) 0
          ([]++[(((M.length-1:Nat)):Int)]) from by
    unfold Trans.Recal.fAnc
    rw [if_neg (by unfold Trans.Recal.lenI; omega)]
    rfl]
  rw [fAncAux_of_chain hpar hlt hzero (M.length+1) (M.length-1) [] (by omega) (by omega)]
  simp only [Option.getD_some]
  rw [show (((M.length-1:Nat)):Int)+1=(((M.length:Nat)):Int) from by omega,
    slice_full,show (0:Int)-1=-1 from by omega]
  obtain ⟨j,hj⟩ : ∃ j, M.length=j+1 := ⟨M.length-1,by omega⟩
  rw [hj,ppairAux_step,if_pos (by omega)]

end Rows.Ladder
