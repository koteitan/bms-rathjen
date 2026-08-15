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

end Rows.Ladder
