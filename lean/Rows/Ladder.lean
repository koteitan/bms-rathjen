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

/-! ## `trMax`, `firstNodes`, `joints`

`trMax` は「`isParentP M 1 (j+1) j` が最初に破れる `j`」でしかない。
枝が 1 本なら `firstNodes` と `joints` はそこから直ちに出る。 -/

theorem trMaxAux_step (M : Trans.Recal.PS) (f : Nat) (j : Int) :
    Trans.Recal.trMaxAux (f+1) M j
      = if j ≥ Trans.Recal.lenI M then Trans.Recal.lenI M-1
        else if !(Trans.Recal.isParentP M 1 (j+1) j) then j
             else Trans.Recal.trMaxAux f M (j+1) := rfl

/-- **`trMax` は最初に親でなくなる位置。** -/
theorem trMax_eq (M : Trans.Recal.PS) (t : Nat) (hlen : t<M.length)
    (hkeep : ∀ j : Nat, j<t →
      Trans.Recal.isParentP M 1 (((j:Nat):Int)+1) ((j:Nat):Int)=true)
    (hstop : Trans.Recal.isParentP M 1 (((t:Nat):Int)+1) ((t:Nat):Int)=false) :
    Trans.Recal.trMax M=((t:Nat):Int) := by
  have key : ∀ (f j : Nat), j ≤ t → t-j<f →
      Trans.Recal.trMaxAux f M ((j:Nat):Int)=((t:Nat):Int) := by
    intro f
    induction f with
    | zero => intro j _ h; exact absurd h (by omega)
    | succ f ih =>
      intro j hjt hf
      rw [trMaxAux_step,if_neg (by unfold Trans.Recal.lenI; omega)]
      by_cases hj : j=t
      · subst hj
        rw [hstop]
        simp
      · rw [hkeep j (by omega)]
        simp only [Bool.not_true,Bool.false_eq_true,if_false]
        rw [show ((j:Nat):Int)+1=(((j+1:Nat)):Int) from by omega]
        exact ih (j+1) (by omega) (by omega)
  show Trans.Recal.trMaxAux (M.length+1) M ((0:Nat):Int)=((t:Nat):Int)
  exact key (M.length+1) 0 (by omega) (by omega)

theorem firstNodes_single (M B : Trans.Recal.PS) (hbr : Trans.Recal.brF M=[B]) :
    Trans.Recal.firstNodes M
      = [Trans.Recal.trMax M+1,Trans.Recal.trMax M+1+((B.length:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [hbr]
  simp only [List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,
    List.nil_append,List.cons_append]
  rw [show Trans.Recal.trMax M+1+0=Trans.Recal.trMax M+1 from by omega,
    show (0:Int)+((B.length:Nat):Int)=((B.length:Nat):Int) from by omega]

theorem joints_single (M B : Trans.Recal.PS) (hbr : Trans.Recal.brF M=[B]) :
    Trans.Recal.joints M=[Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1) 0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_single M B hbr]
  rfl

/-! ## 枝が 1 本の畳み込み

`red` の第 1 分岐は、枝が 1 本のとき `jjSeq 0 (trMax M)` を切り出して
枝の再構成に降りるだけになる。梯子に依らない形で 1 度だけ書く。 -/

theorem red_fold_single (M : Trans.Recal.PS) (f : Nat) (tr nJ jnJ : Int)
    (B : Trans.Recal.PS)
    (hzero : Trans.Recal.isZeroP M=false)
    (hprin : Trans.Recal.isPrincipalP M=true)
    (hg0 : Trans.Recal.gp0 M 0=0) (hg1 : Trans.Recal.gp1 M 0=0)
    (htr : Trans.Recal.trMax M=tr)
    (hne : (tr==Trans.Recal.lenI M-1)=false)
    (hbr : Trans.Recal.brF M=[B])
    (hjn : Trans.Recal.fpar M 0 (tr+1) 0=jnJ)
    (hnJ : (if (Trans.Recal.gp1 B 0==0)=true then (-1:Int)
            else Trans.Recal.fpar M 1 (tr+1) 0)=nJ) :
    Trans.Recal.red (f+1) M
      = Trans.Recal.jjSeq 0 tr
        ++ Trans.Recal.incrFirst
             (Trans.Recal.red f ((jnJ+1,nJ+1) :: Trans.Recal.derp B)) (jnJ-nJ) := by
  have hfn : (Trans.Recal.firstNodes M).getD 0 0=tr+1 := by
    rw [firstNodes_single M B hbr,htr]
    rfl
  have hjn' : (Trans.Recal.joints M).getD 0 0=jnJ := by
    rw [joints_single M B hbr,htr]
    exact hjn
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
  rw [hfn,hjn',hnJ]

/-- 切り出しだけで終わる場合: `trMax` が末尾に届いている。 -/
theorem red_jj (M : Trans.Recal.PS) (f : Nat)
    (hzero : Trans.Recal.isZeroP M=false)
    (hprin : Trans.Recal.isPrincipalP M=true)
    (hg0 : Trans.Recal.gp0 M 0=0) (hg1 : Trans.Recal.gp1 M 0=0)
    (htr : Trans.Recal.trMax M=Trans.Recal.lenI M-1) :
    Trans.Recal.red (f+1) M=Trans.Recal.jjSeq 0 (Trans.Recal.lenI M-1) := by
  simp only [Trans.Recal.red]
  rw [hzero]
  simp only [Bool.false_eq_true,if_false]
  rw [hprin]
  simp only [if_true]
  rw [hg0,hg1]
  rw [show ((0:Int)==0)=true from rfl]
  simp only [Bool.and_self,if_true]
  rw [htr,show (Trans.Recal.lenI M-1==Trans.Recal.lenI M-1)=true from by simp]
  simp only [if_true]

/-- 零の梯子。 -/
theorem red_zeroP (M : Trans.Recal.PS) (f : Nat) (h : Trans.Recal.isZeroP M=true) :
    Trans.Recal.red (f+1) M=Trans.Recal.zeroPS := by
  simp only [Trans.Recal.red]
  rw [h]
  simp only [if_true]

/-- 長さ 1 の梯子は、行 1 が 0 でなければ主要。 -/
theorem isPrincipalP_single (a b : Int) (hb : (b==0)=false) :
    Trans.Recal.isPrincipalP [(a,b)]=true := by
  unfold Trans.Recal.isPrincipalP Trans.Recal.isZeroP Trans.Recal.isAnc
  rw [show Trans.Recal.gp1 [(a,b)] 0=b from rfl,hb]
  simp only [Bool.and_false,Bool.not_false]
  rw [if_neg (by unfold Trans.Recal.lenI; simp)]
  rfl

theorem fpar1_unfold (M : Trans.Recal.PS) (j k : Int)
    (h : ¬(j<0 ∨ j ≥ Trans.Recal.lenI M)) :
    Trans.Recal.fpar M 1 j k
      = Trans.Recal.fpar1Aux (M.length+1) M (Trans.Recal.gp1 M j) j k := by
  unfold Trans.Recal.fpar
  rw [if_neg h]
  rfl

theorem fpar1Aux_step (M : Trans.Recal.PS) (f : Nat) (tgt j0 kk : Int) :
    Trans.Recal.fpar1Aux (f+1) M tgt j0 kk
      = (if Trans.Recal.fpar0 M j0 kk<kk then -1
         else if Trans.Recal.gp1 M (Trans.Recal.fpar0 M j0 kk)<tgt then
           Trans.Recal.fpar0 M j0 kk
         else Trans.Recal.fpar1Aux f M tgt (Trans.Recal.fpar0 M j0 kk) kk) := rfl

theorem fpar_out (M : Trans.Recal.PS) (i : Nat) (j k : Int)
    (h : j ≥ Trans.Recal.lenI M) : Trans.Recal.fpar M i j k=-1 := by
  unfold Trans.Recal.fpar
  rw [if_pos (Or.inr h)]

theorem isParentP_of_fpar (M : Trans.Recal.PS) (i : Nat) (j k : Int)
    (hk0 : 0 ≤ k) (hk1 : k<Trans.Recal.lenI M) (h : Trans.Recal.fpar M i j k=k) :
    Trans.Recal.isParentP M i j k=true := by
  unfold Trans.Recal.isParentP
  rw [h,decide_eq_true hk0,decide_eq_true hk1]
  simp

theorem isParentP_of_ne (M : Trans.Recal.PS) (i : Nat) (j k v : Int)
    (h : Trans.Recal.fpar M i j k=v) (hv : v ≠ k) :
    Trans.Recal.isParentP M i j k=false := by
  unfold Trans.Recal.isParentP
  rw [h,show (k==v)=false from beq_eq_false_iff_ne.mpr (fun hc => hv hc.symm)]
  simp

theorem fpar0_eq (M : Trans.Recal.PS) (j k : Int) :
    Trans.Recal.fpar0 M j k=Trans.Recal.fpar M 0 j k := rfl

/-! ### 小さい添字での親、値の比較だけから

`trMax` と `joints`・`nJ` が要るのは添字 1・2・3 の親だけである。
そこは走査が 1〜2 歩で終わるので、`gp0`・`gp1` の大小だけで決まる。 -/

theorem fpar0_one (M : Trans.Recal.PS) (hlen : 2 ≤ M.length)
    (h : Trans.Recal.gp0 M 0<Trans.Recal.gp0 M 1) : Trans.Recal.fpar0 M 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  rw [fpar0Aux_step,if_neg (by omega),show (1:Int)-1=0 from by omega,if_pos h]

theorem fpar0_two_lb (M : Trans.Recal.PS) (hlen : 3 ≤ M.length)
    (h : Trans.Recal.gp0 M 1<Trans.Recal.gp0 M 2) : Trans.Recal.fpar0 M 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  rw [show (2:Int)-1=1 from by omega,fpar0Aux_step,if_neg (by omega),if_pos h]

theorem fpar0_one_lb (M : Trans.Recal.PS) (hlen : 2 ≤ M.length) :
    Trans.Recal.fpar0 M 1 1=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  rw [show (1:Int)-1=0 from by omega,fpar0Aux_step,if_pos (by omega)]

theorem fpar0_three_lb (M : Trans.Recal.PS) (hlen : 4 ≤ M.length)
    (h : ¬(Trans.Recal.gp0 M 2<Trans.Recal.gp0 M 3)) : Trans.Recal.fpar0 M 3 2=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  obtain ⟨g,hg⟩ : ∃ g, M.length=g+1 := ⟨M.length-1,by omega⟩
  rw [hg,show (3:Int)-1=2 from by omega,fpar0Aux_step,if_neg (by omega),if_neg h,
    show (2:Int)-1=1 from by omega]
  obtain ⟨g2,hg2⟩ : ∃ g2, g=g2+1 := ⟨g-1,by omega⟩
  rw [hg2,fpar0Aux_step,if_pos (by omega)]

theorem fpar1_one (M : Trans.Recal.PS) (hlen : 2 ≤ M.length)
    (h : Trans.Recal.gp0 M 0<Trans.Recal.gp0 M 1)
    (hq : Trans.Recal.gp1 M 0<Trans.Recal.gp1 M 1) : Trans.Recal.fpar M 1 1 0=0 := by
  rw [fpar1_unfold M 1 0 (by unfold Trans.Recal.lenI; omega)]
  rw [fpar1Aux_step,fpar0_one M hlen h,if_neg (by omega),if_pos hq]

theorem fpar1_two_lb (M : Trans.Recal.PS) (hlen : 3 ≤ M.length)
    (h : Trans.Recal.gp0 M 1<Trans.Recal.gp0 M 2)
    (hq : ¬(Trans.Recal.gp1 M 1<Trans.Recal.gp1 M 2)) : Trans.Recal.fpar M 1 2 1=-1 := by
  rw [fpar1_unfold M 2 1 (by unfold Trans.Recal.lenI; omega)]
  obtain ⟨g,hg⟩ : ∃ g, M.length=g+1 := ⟨M.length-1,by omega⟩
  rw [hg,fpar1Aux_step,fpar0_two_lb M hlen h,if_neg (by omega),if_neg hq]
  obtain ⟨g2,hg2⟩ : ∃ g2, g=g2+1 := ⟨g-1,by omega⟩
  rw [hg2,fpar1Aux_step,fpar0_one_lb M (by omega),if_pos (by omega)]

theorem fpar1_two_lb_eq (M : Trans.Recal.PS) (hlen : 3 ≤ M.length)
    (h : Trans.Recal.gp0 M 1<Trans.Recal.gp0 M 2)
    (hq : Trans.Recal.gp1 M 1<Trans.Recal.gp1 M 2) : Trans.Recal.fpar M 1 2 1=1 := by
  rw [fpar1_unfold M 2 1 (by unfold Trans.Recal.lenI; omega)]
  rw [fpar1Aux_step,fpar0_two_lb M hlen h,if_neg (by omega),if_pos hq]

theorem fpar1_three_lb (M : Trans.Recal.PS) (hlen : 4 ≤ M.length)
    (h : ¬(Trans.Recal.gp0 M 2<Trans.Recal.gp0 M 3)) : Trans.Recal.fpar M 1 3 2=-1 := by
  rw [fpar1_unfold M 3 2 (by unfold Trans.Recal.lenI; omega)]
  rw [fpar1Aux_step,fpar0_three_lb M hlen h,if_pos (by omega)]

theorem fpar1_two_zero (M : Trans.Recal.PS) (hlen : 3 ≤ M.length)
    (hp : Trans.Recal.fpar M 0 2 0=1)
    (h : Trans.Recal.gp0 M 0<Trans.Recal.gp0 M 1)
    (hq1 : ¬(Trans.Recal.gp1 M 1<Trans.Recal.gp1 M 2))
    (hq0 : Trans.Recal.gp1 M 0<Trans.Recal.gp1 M 2) : Trans.Recal.fpar M 1 2 0=0 := by
  rw [fpar1_unfold M 2 0 (by unfold Trans.Recal.lenI; omega)]
  obtain ⟨g,hg⟩ : ∃ g, M.length=g+1 := ⟨M.length-1,by omega⟩
  rw [hg,fpar1Aux_step,show Trans.Recal.fpar0 M 2 0=1 from by rw [fpar0_eq]; exact hp,
    if_neg (by omega),if_neg hq1]
  obtain ⟨g2,hg2⟩ : ∃ g2, g=g2+1 := ⟨g-1,by omega⟩
  rw [hg2,fpar1Aux_step,fpar0_one M (by omega) h,if_neg (by omega),if_pos hq0]

theorem fpar1_three_zero (M : Trans.Recal.PS) (hlen : 4 ≤ M.length)
    (hp : Trans.Recal.fpar M 0 3 0=0)
    (hq0 : Trans.Recal.gp1 M 0<Trans.Recal.gp1 M 3) : Trans.Recal.fpar M 1 3 0=0 := by
  rw [fpar1_unfold M 3 0 (by unfold Trans.Recal.lenI; omega)]
  rw [fpar1Aux_step,show Trans.Recal.fpar0 M 3 0=0 from by rw [fpar0_eq]; exact hp,
    if_neg (by omega),if_pos hq0]

/-! ## 枝が何本でもよい畳み込み

`red_fold_single` は枝が 1 本の場合しか扱わない。`Rows/G11.lean` の梯子は
枝が 4 本・2 本になるので、`foldl` を開いたところで止める形も要る。 -/

theorem red_fold_open (M : Trans.Recal.PS) (f : Nat) (tr : Int)
    (hzero : Trans.Recal.isZeroP M=false)
    (hprin : Trans.Recal.isPrincipalP M=true)
    (hg0 : Trans.Recal.gp0 M 0=0) (hg1 : Trans.Recal.gp1 M 0=0)
    (htr : Trans.Recal.trMax M=tr)
    (hne : (tr==Trans.Recal.lenI M-1)=false) :
    Trans.Recal.red (f+1) M
      = (List.range (Trans.Recal.brF M).length).foldl
          (init := Trans.Recal.jjSeq 0 tr) (fun r J =>
            let bJ := (Trans.Recal.brF M).getD J []
            let nJ : Int := if Trans.Recal.gp1 bJ 0==0 then -1
              else Trans.Recal.fpar M 1 ((Trans.Recal.firstNodes M).getD J 0) 0
            let jnJ := (Trans.Recal.joints M).getD J 0
            r ++ Trans.Recal.incrFirst
              (Trans.Recal.red f ((jnJ+1,nJ+1) :: Trans.Recal.derp bJ)) (jnJ-nJ)) := by
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

theorem firstNodes_eq (M : Trans.Recal.PS) (br : List Trans.Recal.PS)
    (hbr : Trans.Recal.brF M=br) :
    Trans.Recal.firstNodes M
      = (Trans.Recal.idxSum br).map (fun e => Trans.Recal.trMax M+1+e) := by
  unfold Trans.Recal.firstNodes
  rw [hbr]

theorem joints_eq (M : Trans.Recal.PS) (br : List Trans.Recal.PS)
    (hbr : Trans.Recal.brF M=br) :
    Trans.Recal.joints M
      = (((Trans.Recal.idxSum br).map
          (fun e => Trans.Recal.trMax M+1+e)).dropLast).map
            (fun e => Trans.Recal.fpar M 0 e 0) := by
  unfold Trans.Recal.joints
  rw [firstNodes_eq M br hbr]

/-! ## 頭が主要でない 2 つの枝

`gp0 M 0 ≠ 0` のとき `red` は畳み込まない。行 1 が `0` なら頭を `0` に正規化するだけ、
`1` なら 1 列切り出して降り、戻ってきた列を落とす。どちらも梯子に依らない。 -/

theorem red_shift (M : Trans.Recal.PS) (f : Nat)
    (hzero : Trans.Recal.isZeroP M=false)
    (hprin : Trans.Recal.isPrincipalP M=true)
    (hg0 : (Trans.Recal.gp0 M 0==0)=false)
    (hg1 : Trans.Recal.gp1 M 0=0) :
    Trans.Recal.red (f+1) M
      = Trans.Recal.red f (Trans.Recal.incrFirst M (-(Trans.Recal.gp0 M 0))) := by
  simp only [Trans.Recal.red]
  rw [hzero]
  simp only [Bool.false_eq_true,if_false]
  rw [hprin]
  simp only [if_true]
  rw [hg0]
  simp only [Bool.false_and,Bool.false_eq_true,if_false]
  rw [hg1,show ((0:Int)==0)=true from rfl]
  simp only [if_true]

theorem red_head_one (M : Trans.Recal.PS) (f : Nat) (W : Trans.Recal.PS)
    (hzero : Trans.Recal.isZeroP M=false)
    (hprin : Trans.Recal.isPrincipalP M=true)
    (hg0 : (Trans.Recal.gp0 M 0==0)=false)
    (hg1 : Trans.Recal.gp1 M 0=1)
    (hA : Trans.Recal.red f (((0:Int),(0:Int)) :: Trans.Recal.incrFirst M 1)
      = ((0:Int),(0:Int)) :: W)
    (hWlen : 1 ≤ W.length)
    (hWprin : Trans.Recal.isPrincipalP W=true)
    (hW : Trans.Recal.gp0 W 0=Trans.Recal.gp1 W 0) :
    Trans.Recal.red (f+1) M=W := by
  have hNdrop : (((0:Int),(0:Int)) :: W).drop 1=W := rfl
  have hgw0 : Trans.Recal.gp0 (((0:Int),(0:Int)) :: W) 1=Trans.Recal.gp0 W 0 := rfl
  have hgw1 : Trans.Recal.gp1 (((0:Int),(0:Int)) :: W) 1=Trans.Recal.gp1 W 0 := rfl
  simp only [Trans.Recal.red]
  rw [hzero]
  simp only [Bool.false_eq_true,if_false]
  rw [hprin]
  simp only [if_true]
  rw [hg0]
  simp only [Bool.false_and,Bool.false_eq_true,if_false]
  rw [hg1,show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Recal.jjSeq 0 ((1:Int)-1)=[((0:Int),(0:Int))] from rfl]
  show (let N := Trans.Recal.red f ([((0:Int),(0:Int))]++Trans.Recal.incrFirst M 1)
    let jN : Int := Trans.Recal.lenI N-1
    if decide ((1:Int) ≤ jN) && Trans.Recal.isPrincipalP (N.drop (1:Int).toNat) then
      Trans.Recal.incrFirst (N.drop (1:Int).toNat)
        (-(Trans.Recal.gp0 N 1)+Trans.Recal.gp1 N 1)
    else M)=W
  rw [show ([((0:Int),(0:Int))]++Trans.Recal.incrFirst M 1)
      =((0:Int),(0:Int)) :: Trans.Recal.incrFirst M 1 from rfl,hA]
  show (if decide ((1:Int) ≤ Trans.Recal.lenI (((0:Int),(0:Int)) :: W)-1)
      && Trans.Recal.isPrincipalP ((((0:Int),(0:Int)) :: W).drop 1) then
    Trans.Recal.incrFirst ((((0:Int),(0:Int)) :: W).drop 1)
      (-(Trans.Recal.gp0 (((0:Int),(0:Int)) :: W) 1)
        +Trans.Recal.gp1 (((0:Int),(0:Int)) :: W) 1)
    else M)=W
  rw [hNdrop,hgw0,hgw1,hW,hWprin,
    show decide ((1:Int) ≤ Trans.Recal.lenI (((0:Int),(0:Int)) :: W)-1)=true from
      decide_eq_true (by
        unfold Trans.Recal.lenI
        rw [List.length_cons]
        omega)]
  simp only [Bool.and_self,if_true]
  rw [show -(Trans.Recal.gp1 W 0)+Trans.Recal.gp1 W 0=(0:Int) from by omega]
  unfold Trans.Recal.incrFirst
  rw [show (fun c : Int × Int => (c.1+0,c.2))=id from by
    funext c
    show (c.1+0,c.2)=c
    rw [Int.add_zero]]
  exact List.map_id _

/-! ## 根がいくつか並んだあとに 1 本の鎖

`Rows/G11.lean` の梯子は 1 つの主要ブロックにならない。`ppair` は先頭側に
1 列ずつの根をいくつか出し、そのあと残り全部を 1 ブロックにする。
その形を一度だけ書く。 -/

theorem fAncAux_of_chain_at {p : Nat}
    (hpar : ∀ k, p<k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int))
    (hlt : ∀ k, p<k → k<M.length → par k<k)
    (hge : ∀ k, p<k → k<M.length → p ≤ par k)
    (hroot : Trans.Recal.fpar M 0 ((p:Nat):Int) 0=-1) :
    ∀ (f k : Nat) (acc : List Int), p ≤ k → k<M.length → k-p<f →
      (Trans.Recal.fAncAux f M 0 ((k:Nat):Int) 0 (acc++[((k:Nat):Int)])).getLast?
        = some ((p:Nat):Int) := by
  intro f
  induction f with
  | zero => intro k _ _ _ h; exact absurd h (by omega)
  | succ f ih =>
    intro k acc hpk hk hkf
    rw [fAncAux_step]
    by_cases h0 : k=p
    · subst h0
      rw [hroot,if_neg (by omega)]
      simp
    · have hpk' : p<k := by omega
      rw [hpar k hpk' hk,if_pos (by
        have := hge k hpk' hk
        omega)]
      have := ih (par k) (acc++[((k:Nat):Int)])
        (hge k hpk' hk)
        (by have := hlt k hpk' hk; omega)
        (by have := hlt k hpk' hk; have := hge k hpk' hk; omega)
      simpa only [List.append_assoc] using this

theorem ppairAux_roots (p : Nat) (hp : p<M.length)
    (hroots : ∀ j, j<p → Trans.Recal.fpar M 0 ((j:Nat):Int) 0=-1) :
    ∀ (f j : Nat) (acc : List Trans.Recal.PS), j ≤ p → j<f+1 →
      Trans.Recal.ppairAux f M ((((j:Nat)):Int)-1) acc
        = (List.range j).map
            (fun i => Trans.Recal.slice M ((i:Nat):Int) ((((i:Nat)):Int)+1)) ++ acc := by
  intro f
  induction f with
  | zero =>
    intro j acc hj hjf
    have : j=0 := by omega
    subst this
    show Trans.Recal.ppairAux 0 M ((((0:Nat)):Int)-1) acc=_
    simp [Trans.Recal.ppairAux]
  | succ f ih =>
    intro j acc hj hjf
    cases j with
    | zero =>
      rw [ppairAux_step,if_pos (by omega)]
      simp
    | succ j =>
      rw [show ((((j+1:Nat)):Int)-1)=((j:Nat):Int) from by omega,
        ppairAux_step,if_neg (by omega)]
      rw [show Trans.Recal.fAnc M 0 ((j:Nat):Int) 0=[((j:Nat):Int)] from by
        unfold Trans.Recal.fAnc
        rw [if_neg (by
          refine not_or.mpr ⟨by omega,?_⟩
          unfold Trans.Recal.lenI
          omega)]
        obtain ⟨g,hg⟩ : ∃ g, M.length+1=g+1 := ⟨M.length,rfl⟩
        rw [hg,fAncAux_step,hroots j (by omega),if_neg (by omega)]]
      simp only [List.getLast?_singleton,Option.getD_some]
      rw [ih j (Trans.Recal.slice M ((j:Nat):Int) (((j:Nat):Int)+1) :: acc)
        (by omega) (by omega),List.range_succ,List.map_append]
      simp

/-- **根が `p` 本、そのあと 1 ブロック。** -/
theorem ppair_roots_then_block (p : Nat) (hp : p<M.length)
    (hroots : ∀ j, j<p → Trans.Recal.fpar M 0 ((j:Nat):Int) 0=-1)
    (hpar : ∀ k, p<k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
      = ((par k : Nat) : Int))
    (hlt : ∀ k, p<k → k<M.length → par k<k)
    (hge : ∀ k, p<k → k<M.length → p ≤ par k)
    (hroot : Trans.Recal.fpar M 0 ((p:Nat):Int) 0=-1) :
    Trans.Recal.ppair M
      = (List.range p).map
          (fun i => Trans.Recal.slice M ((i:Nat):Int) ((((i:Nat)):Int)+1))
        ++ [Trans.Recal.slice M ((p:Nat):Int) ((M.length:Nat):Int)] := by
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
  rw [fAncAux_of_chain_at hpar hlt hge hroot (M.length+1) (M.length-1) []
    (by omega) (by omega) (by omega)]
  simp only [Option.getD_some]
  rw [show (((M.length-1:Nat)):Int)+1=((M.length:Nat):Int) from by omega]
  rw [show ((p:Nat):Int)-1=((((p:Nat)):Int)-1) from rfl]
  exact ppairAux_roots p hp hroots M.length p
    [Trans.Recal.slice M ((p:Nat):Int) ((M.length:Nat):Int)] (by omega) (by omega)

/-! ## 下限つきの親、そして根の判定

`ppair_roots_then_block` を使う梯子では、下の数本は親を持たない。だから
「`p` より上でだけ親が言える」形と、「これ以下に小さい値がないから根」という形が要る。 -/

theorem fpar_of_gap_at {p : Nat}
    (hg : ∀ k, k<M.length → Trans.Recal.gp0 M ((k:Nat):Int)=G k)
    (hlt : ∀ k, p<k → k<M.length → par k<k)
    (hge : ∀ k, p<k → k<M.length → p ≤ par k)
    (hdrop : ∀ k, p<k → k<M.length → G (par k)<G k)
    (hkeep : ∀ k i, p<k → k<M.length → par k<i → i<k → G k ≤ G i) :
    ∀ k, p<k → k<M.length → Trans.Recal.fpar M 0 ((k:Nat):Int) 0
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

theorem fpar0Aux_nofind
    (hg : ∀ k, k<M.length → Trans.Recal.gp0 M ((k:Nat):Int)=G k)
    {j : Nat} (hj : j<M.length) (hmin : ∀ i, i<j → G j ≤ G i) :
    ∀ (f jj : Nat), jj<j → jj+2 ≤ f →
      Trans.Recal.fpar0Aux f M (G j) ((jj:Nat):Int) 0=-1 := by
  intro f
  induction f with
  | zero => intro jj _ h; exact absurd h (by omega)
  | succ f ih =>
    intro jj hjj hf
    rw [fpar0Aux_step,if_neg (by omega),hg jj (by omega),
      if_neg (by have := hmin jj hjj; omega)]
    by_cases h0 : jj=0
    · subst h0
      rw [show ((0:Nat):Int)-1=-1 from by omega]
      obtain ⟨g,hg2⟩ : ∃ g, f=g+1 := ⟨f-1,by omega⟩
      rw [hg2,fpar0Aux_step,if_pos (by omega)]
    · obtain ⟨u,rfl⟩ : ∃ u, jj=u+1 := ⟨jj-1,by omega⟩
      rw [show (((u+1:Nat)):Int)-1=((u:Nat):Int) from by omega]
      exact ih u (by omega) (by omega)

/-- **根の判定。** 自分より下に小さい行 0 の値がなければ親は無い。 -/
theorem fpar_root_of_min
    (hg : ∀ k, k<M.length → Trans.Recal.gp0 M ((k:Nat):Int)=G k)
    {j : Nat} (hj : j<M.length) (hmin : ∀ i, i<j → G j ≤ G i) :
    Trans.Recal.fpar M 0 ((j:Nat):Int) 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; omega)]
  simp only [show ((0:Nat)==0)=true from rfl,if_true]
  rw [hg j hj]
  by_cases h0 : j=0
  · subst h0
    rw [show ((0:Nat):Int)-1=-1 from by omega]
    obtain ⟨g,hg2⟩ : ∃ g, M.length+1=g+1 := ⟨M.length,rfl⟩
    rw [hg2,fpar0Aux_step,if_pos (by omega)]
  · obtain ⟨u,rfl⟩ : ∃ u, j=u+1 := ⟨j-1,by omega⟩
    rw [show (((u+1:Nat)):Int)-1=((u:Nat):Int) from by omega]
    exact fpar0Aux_nofind hg hj hmin (M.length+1) u (by omega) (by omega)

/-- 行 1 の親が根そのもの。 -/
theorem fpar1_at_zero (M : Trans.Recal.PS) (j : Int) (hj0 : 0 ≤ j)
    (hjl : j<Trans.Recal.lenI M) (hlen : 1 ≤ M.length)
    (hp : Trans.Recal.fpar M 0 j 0=0)
    (hq0 : Trans.Recal.gp1 M 0<Trans.Recal.gp1 M j) : Trans.Recal.fpar M 1 j 0=0 := by
  rw [fpar1_unfold M j 0 (by omega)]
  obtain ⟨g,hg⟩ : ∃ g, M.length+1=g+1 := ⟨M.length,rfl⟩
  rw [hg,fpar1Aux_step,show Trans.Recal.fpar0 M j 0=0 from by rw [fpar0_eq]; exact hp,
    if_neg (by omega),if_pos hq0]

/-- 行 1 の親、行 0 の親が添字 1 のとき。 -/
theorem fpar1_via_one (M : Trans.Recal.PS) (j : Int) (hj0 : 0 ≤ j)
    (hjl : j<Trans.Recal.lenI M) (hlen : 2 ≤ M.length)
    (hp : Trans.Recal.fpar M 0 j 0=1)
    (h01 : Trans.Recal.gp0 M 0<Trans.Recal.gp0 M 1)
    (hq1 : ¬(Trans.Recal.gp1 M 1<Trans.Recal.gp1 M j))
    (hq0 : Trans.Recal.gp1 M 0<Trans.Recal.gp1 M j) : Trans.Recal.fpar M 1 j 0=0 := by
  rw [fpar1_unfold M j 0 (by omega)]
  obtain ⟨g,hg⟩ : ∃ g, M.length=g+1 := ⟨M.length-1,by omega⟩
  rw [hg,fpar1Aux_step,show Trans.Recal.fpar0 M j 0=1 from by rw [fpar0_eq]; exact hp,
    if_neg (by omega),if_neg hq1]
  obtain ⟨g2,hg2⟩ : ∃ g2, g=g2+1 := ⟨g-1,by omega⟩
  rw [hg2,fpar1Aux_step,fpar0_one M (by omega) h01,if_neg (by omega),if_pos hq0]

/-! ## 枝が 4 本・2 本のときの `firstNodes` と `joints` -/

theorem firstNodes_four (M B0 B1 B2 B3 : Trans.Recal.PS)
    (hbr : Trans.Recal.brF M=[B0,B1,B2,B3]) :
    Trans.Recal.firstNodes M
      = [Trans.Recal.trMax M+1+0,
         Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)),
         Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)+((B1.length:Nat):Int)),
         Trans.Recal.trMax M+1
           +(0+((B0.length:Nat):Int)+((B1.length:Nat):Int)+((B2.length:Nat):Int)),
         Trans.Recal.trMax M+1
           +(0+((B0.length:Nat):Int)+((B1.length:Nat):Int)+((B2.length:Nat):Int)
             +((B3.length:Nat):Int))] := by
  rw [firstNodes_eq M _ hbr]
  rfl

theorem joints_four (M B0 B1 B2 B3 : Trans.Recal.PS)
    (hbr : Trans.Recal.brF M=[B0,B1,B2,B3]) :
    Trans.Recal.joints M
      = [Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1+0) 0,
         Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int))) 0,
         Trans.Recal.fpar M 0
           (Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)+((B1.length:Nat):Int))) 0,
         Trans.Recal.fpar M 0
           (Trans.Recal.trMax M+1
             +(0+((B0.length:Nat):Int)+((B1.length:Nat):Int)+((B2.length:Nat):Int)))
           0] := by
  rw [joints_eq M _ hbr]
  rfl

theorem firstNodes_two (M B0 B1 : Trans.Recal.PS) (hbr : Trans.Recal.brF M=[B0,B1]) :
    Trans.Recal.firstNodes M
      = [Trans.Recal.trMax M+1+0,
         Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)),
         Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)+((B1.length:Nat):Int))] := by
  rw [firstNodes_eq M _ hbr]
  rfl

theorem joints_two (M B0 B1 : Trans.Recal.PS) (hbr : Trans.Recal.brF M=[B0,B1]) :
    Trans.Recal.joints M
      = [Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1+0) 0,
         Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int))) 0] := by
  rw [joints_eq M _ hbr]
  rfl

theorem firstNodes_three (M B0 B1 B2 : Trans.Recal.PS)
    (hbr : Trans.Recal.brF M=[B0,B1,B2]) :
    Trans.Recal.firstNodes M
      = [Trans.Recal.trMax M+1+0,
         Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)),
         Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)+((B1.length:Nat):Int)),
         Trans.Recal.trMax M+1
           +(0+((B0.length:Nat):Int)+((B1.length:Nat):Int)+((B2.length:Nat):Int))] := by
  rw [firstNodes_eq M _ hbr]
  rfl

theorem joints_three (M B0 B1 B2 : Trans.Recal.PS)
    (hbr : Trans.Recal.brF M=[B0,B1,B2]) :
    Trans.Recal.joints M
      = [Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1+0) 0,
         Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int))) 0,
         Trans.Recal.fpar M 0
           (Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int)+((B1.length:Nat):Int)))
           0] := by
  rw [joints_eq M _ hbr]
  rfl

theorem firstNodes_one (M B0 : Trans.Recal.PS) (hbr : Trans.Recal.brF M=[B0]) :
    Trans.Recal.firstNodes M
      = [Trans.Recal.trMax M+1+0,
         Trans.Recal.trMax M+1+(0+((B0.length:Nat):Int))] := by
  rw [firstNodes_eq M _ hbr]
  rfl

theorem joints_one (M B0 : Trans.Recal.PS) (hbr : Trans.Recal.brF M=[B0]) :
    Trans.Recal.joints M=[Trans.Recal.fpar M 0 (Trans.Recal.trMax M+1+0) 0] := by
  rw [joints_eq M _ hbr]
  rfl

end Rows.Ladder
