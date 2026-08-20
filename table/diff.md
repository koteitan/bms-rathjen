# 作業ツリー

## 注意書き

> **これからやることのリスト。** 埋まったら ✅ を付ける。
>
> 日記ではない。**やったことを後から書かない。**
> 各項目は**タイトルだけ**を短く書く。根拠・測定値・補題名・経緯は書かない。
> **括弧書きによる付加情報も禁止**する。
> 子がすべて ✅ になったツリーは**閉じて、親を ✅ にする**。
> 印は 🚨 未着手 / 🚨🤖 着手中 / ✅ 完了 の 3 つだけ。
> 他の目的に使わない。済んだ作業の記録は [findings.md](findings.md) に置く。
>
> **この注意書きより下は、作業項目だけを置く。**

## ツリー

- 🚨 選定 23 行に [E.cert](table-r1.md#ecert) を付ける
 - 🚨 326 行目に [E.cert](table-r1.md#ecert) を付ける
  - 🚨 [D.Certified.lim](table-r1.md#dcertifiedlim) の $`t \in \mathfrak{T}(M)`$ と $`f_n \in \mathfrak{T}(M)`$ を供給する
   - 🚨 `PsiIdxOKStd172` を証明するか反証する
  - 🚨 [D.Certified.lim](table-r1.md#dcertifiedlim) の $`f_n \lt t`$ と $`f_n \lt f_{n+1}`$ を供給する
   - 🚨 `HiMono89` を証明するか反証する
  - 🚨 [D.Certified.lim](table-r1.md#dcertifiedlim) の $`\forall s \lt t.\ \exists n.\ s \le f_n`$ を供給する
   - 🚨 `vOf tGap107` が大きすぎるのか展開の値が小さすぎるのかを決める
   - 🚨 決まった側を直す
   - 🚨 `LimCofS1` を証明する
- 🚨 表の値を直す
 - 🚨 `reg` を直しても順序と `inT` が壊れない道を見つける
 - 🚨 `Trans/Dict.lean` を書き換えてビルドを通す
 - 🚨 壊れている 5 行の `Rows/TM.lean` の値を書き換える
 - 🚨 5 行の注記と表のバナーを外す
- 🚨 Hexirp 氏の表と食い違う 9 行について、どちらが正しいかを決める
 - 🚨 9 行を BMS の順序に並べ、両側の単調性と単射性を測る
 - 🚨 行ごとに当方が正しいか先方が正しいかを書く
 - 🚨 当方が誤っている行があれば表に印を付ける
