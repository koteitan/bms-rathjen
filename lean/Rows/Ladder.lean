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

/-! ## 行 0 の親を `gp0` の形だけから出す

`fpar M 0 k 0` は「`k-1` から下へ走査して最初に `gp0` が下がる位置」である。
だから `gp0` の閉じた形と、親の位置での落差・その間での非落差だけあればよい。 -/

theorem fpar0Aux_step (M : Trans.Recal.PS) (f : Nat) (tgt j0 kk : Int) :
    Trans.Recal.fpar0Aux (f+1) M tgt j0 kk
      = if j0<kk then -1 else if Trans.Recal.gp0 M j0<tgt then j0
        else Trans.Recal.fpar0Aux f M tgt (j0-1) kk := rfl

variable {G : Nat → Int}

/-- 走査は親の位置で止まる。 -/
theorem fpar0Aux_scan
    (hg : ∀ k, k<M.length → Trans.Recal.gp0 M ((k:Nat):Int)=G k)
    {k p : Nat} (hk : k<M.length) (hdrop : G p<G k)
    (hkeep : ∀ i, p<i → i<k → G k ≤ G i) :
    ∀ (f j : Nat), p ≤ j → j<k → j-p<f →
      Trans.Recal.fpar0Aux f M (G k) ((j:Nat):Int) 0=((p:Nat):Int) := by
  intro f
  induction f with
  | zero => intro j _ _ h; exact absurd h (by omega)
  | succ f ih =>
    intro j hpj hjk hf
    rw [fpar0Aux_step,if_neg (by omega),hg j (by omega)]
    by_cases hjp : j=p
    · subst hjp
      rw [if_pos hdrop]
    · rw [if_neg (by
        have := hkeep j (by omega) hjk
        omega)]
      have e : ((j:Nat):Int)-1=(((j-1:Nat)):Int) := by omega
      rw [e]
      exact ih (j-1) (by omega) (by omega) (by omega)

/-- **行 0 の親、`gp0` の形から。** -/
theorem fpar_of_gap
    (hg : ∀ k, k<M.length → Trans.Recal.gp0 M ((k:Nat):Int)=G k)
    (hlt : ∀ k, 1 ≤ k → k<M.length → par k<k)
    (hdrop : ∀ k, 1 ≤ k → k<M.length → G (par k)<G k)
    (hkeep : ∀ k i, 1 ≤ k → k<M.length → par k<i → i<k → G k ≤ G i) :
    ∀ k, 1 ≤ k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int) := by
  intro k hk1 hk
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  simp only [show ((0:Nat)==0)=true from rfl,if_true]
  rw [hg k hk]
  have e : ((k:Nat):Int)-1=(((k-1:Nat)):Int) := by omega
  rw [e]
  exact fpar0Aux_scan hg hk (hdrop k hk1 hk) (fun i h1 h2 => hkeep k i hk1 hk h1 h2)
    (M.length+1) (k-1) (by have := hlt k hk1 hk; omega) (by omega) (by omega)

/-- 根の親は `-1`。 -/
theorem fpar_zero_of_gap
    (hg : ∀ k, k<M.length → Trans.Recal.gp0 M ((k:Nat):Int)=G k)
    (hlen : 1 ≤ M.length) :
    Trans.Recal.fpar M 0 ((0:Nat):Int) 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  simp only [show ((0:Nat)==0)=true from rfl,if_true]
  obtain ⟨j,hj⟩ : ∃ j, M.length=j+1 := ⟨M.length-1,by omega⟩
  rw [hj,fpar0Aux_step,if_pos (by omega)]

/-! ## 枝が 1 本の畳み込み

`red` の第 1 分岐は、`trMax` が `1` で枝が 1 本のとき、`[(0,0),(1,1)]` を切り出して
枝の再構成に降りるだけになる。梯子に依らない形で 1 度だけ書く。 -/

theorem red_fold_one (M : Trans.Recal.PS) (f : Nat) (nJ jnJ : Int) (B : Trans.Recal.PS)
    (hzero : Trans.Recal.isZeroP M=false)
    (hprin : Trans.Recal.isPrincipalP M=true)
    (hg0 : Trans.Recal.gp0 M 0=0) (hg1 : Trans.Recal.gp1 M 0=0)
    (htr : Trans.Recal.trMax M=1)
    (hne : ((1:Int)==Trans.Recal.lenI M-1)=false)
    (hbr : Trans.Recal.brF M=[B])
    (hfn : (Trans.Recal.firstNodes M).getD 0 0=2)
    (hjn : (Trans.Recal.joints M).getD 0 0=jnJ)
    (hnJ : (if (Trans.Recal.gp1 B 0==0)=true then (-1:Int)
            else Trans.Recal.fpar M 1 2 0)=nJ) :
    Trans.Recal.red (f+1) M
      = Trans.Recal.jjSeq 0 1
        ++ Trans.Recal.incrFirst
             (Trans.Recal.red f ((jnJ+1,nJ+1) :: Trans.Recal.derp B)) (jnJ-nJ) := by
  simp only [Trans.Recal.red]
  rw [hzero]
  simp only [Bool.false_eq_true,if_false]
  rw [hprin]
  simp only [if_true]
  rw [hg0,hg1]
  rw [show ((0:Int)==0)=true from rfl]
  simp only [Bool.and_self,if_true]
  rw [htr,hne]
  simp only [Bool.false_eq_true,if_false]
  rw [hbr]
  simp only [List.length_cons,List.length_nil,List.range_succ,List.range_zero,
    List.foldl_cons,List.foldl_nil,List.nil_append,List.getD_cons_zero]
  rw [hfn,hjn,hnJ]

end Rows.Ladder
