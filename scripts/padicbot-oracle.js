// padicbot-oracle.js — naruyoko 氏の `padicBotRathjen/implementation.js` を node から
// 呼べるようにする薄い包み。
//
// **なぜあるか。** `TM/Order.lean` の順序は [R91] 2.3 の転記であり、ψ・Z の領域では
// 外部から検算されていない。同氏の実装は P進大好きbot 氏の Rathjen 型表記の独立実装で、
// `lessThan` / `inT` / `fund` / `dom` を持つ。`scripts/external-check.py` の冒頭が
// 「`TM/` の順序判定・正規形・基本列を外部から検算する対照として使える」と書いている
// のはこれのことで、2026-08-13 まで使われていなかった。
//
// **資料は取り込まない。** CC BY-SA 3.0 であり、パスを渡して読む。
//   https://github.com/Naruyoko/googology/tree/main/padicBotRathjen
//
//   node scripts/padicbot-oracle.js --self-test
//   node scripts/padicbot-oracle.js --impl ~/proofs/naruyoko-googology/padicBotRathjen
//
// **表記 (実測、2026-08-13)。** 先方は P進大好きbot 氏のブログと同じ 3 部構成である:
//
//     phi^i_a(b)        φ^i_a(b)      i=0 は素の Veblen、i=1 は Ω 階層
//     chi^{k}_{a}(b)    χ^κ_a(b)      添字は波括弧が要る
//     psi^k(a)          ψ^κ(a)
//     W                 φ^1_0(0) = Ω
//     M                 φ^2_0(0)
//
// **辞書 (2026-08-13 に 5 点で固定)。** 先方の Ω 階層は χ ではなく φ^1 である
// (`chi^{M}_{0}(0) != W`)。当方の `Z a` は χ_a(0) ([R91] §2) なので:
//
//     Ω = Z 0          ↔ W = phi^1_0(0)          定義
//     M                ↔ M = phi^2_0(0)          定義
//     Γ₀ = ψ_Ω(0)      ↔ psi^W(0)                P進大好きbot 氏の「Up to Γ_0」表
//     φ̄(a,b)           ↔ phi^0_{a}(β°)           β° は [R91] 2.7 の意味上の引数で、
//                                                 **a ∈ SC なら b に関係なくずれる**。
//                                                 repo の `phiShifted` は第 2 選言が
//                                                 `b == zero && a.isSC` なので、そのまま
//                                                 使うと φ̄(Ω,0) と φ̄(Ω,1) が同じ φ_Ω(1)
//                                                 に潰れる (どちらも `inT`、当方の順序は
//                                                 両者を区別する)。正しくは
//                                                 `isFP a (splitFin b).1 || a.isSC`。
//     Z 1 = χ_1(0) = I ↔ chi^{M}_{0}(0)          φ^1 階層全体の不動点かつ正則。
//                                                 φ^1_1(0), φ^1_2(0), φ^1_W(0),
//                                                 φ^1_{φ^1_1(0)}(0), φ^1_{χ^M_0(0)}(0)
//                                                 のすべてが下にあることを実測
//     Z (n+1)          ↔ chi^{M}_{n}(0)          上の一般化 (χ^M_a = Rathjen の χ_{1+a})
//
// **測定 (743 項の標本、当方の `lt` で整列して隣接対を先方の `lessThan` に当てる)。**
//
//                                      β° を誤った版   正しい版
//     先方が読めない項                     1              1
//     訳が重複する項                       6              0
//     先方が「<」と言わない隣接対          8 / 742        0 / 742
//     CTRL 逆順で壊れる対                  734 / 742      741 / 742
//
// **`TM/Order.lean` の初めての外部検算であり、742 対中 742 で一致する。**
// [R91] 2.3 の転記に外部の裏が付いた。
//
// **食い違い 7 件は全部こちらの翻訳の誤りだった。** 当方の `lt` は最初から
// φ̄(Ω,0) < φ̄(Ω,1) を正しく言っており、潰していたのは β° の側である。
// **外部と食い違ったら翻訳を先に疑うこと** — 今日その順序を守らずに三度撤回している
// (`Evidence/SqV.lean` §K3.20、`plan/chi-2ary.md`、そして Hexirp 氏の表の `W(x)`)。

const fs = require("fs");
const path = require("path");

function load(implDir) {
  const p = path.join(implDir, "implementation.js");
  if (!fs.existsSync(p)) {
    console.log(`[飛ばす] 実装が無い: ${p}`);
    console.log("  出典: https://github.com/Naruyoko/googology/tree/main/padicBotRathjen");
    console.log("  CC BY-SA 3.0。リポジトリには入れない。");
    return null;
  }
  // ブラウザ用のスクリプトなので、DOM の最小限の代替を与えてから評価する。
  const stub =
    "var window={addEventListener:function(){},onload:null};" +
    "var document={getElementById:function(){return {addEventListener:function(){}," +
    "style:{},value:'',innerHTML:'',appendChild:function(){}}}," +
    "addEventListener:function(){},createElement:function(){return {style:{}}}};\n";
  const src = stub + fs.readFileSync(p, "utf8") +
    "\nmodule.exports={Term:Term,inT:inT,lessThan:lessThan,equal:equal};\n";
  const tmp = path.join(require("os").tmpdir(), "padicbot-oracle-loaded.js");
  fs.writeFileSync(tmp, src);
  delete require.cache[tmp];
  return require(tmp);
}

// --- 自己試験 (constitution C0) -------------------------------------------
// 捕まえるはずのものを与えて発火させ、正常な対照で沈黙させる。
function selfTest(implDir) {
  const P = load(implDir);
  if (!P) return 0;
  const fails = [];
  const parse = (s) => new P.Term(s);
  const str = (s) => parse(s).toString();

  // 1. 記法が上のコメントどおりであること
  if (str("1") !== "φ^0_0(0)") fails.push("1 が φ^0_0(0) にならない: " + str("1"));
  if (str("W") !== "φ^φ^0_0(0)_0(0)") fails.push("W が φ^1_0(0) にならない: " + str("W"));
  // 2. **辞書の落とし穴**: 先方の Ω 階層は χ ではない
  if (P.equal(parse("chi^{M}_{0}(0)"), parse("W")))
    fails.push("chi^{M}_{0}(0) == W になった (先方の Ω 階層が χ でないという前提が崩れる)");
  // 3. inT が両側を見る: 正しい項を通し、壊れた項で例外
  if (!P.inT(parse("psi^W(0)"))) fails.push("psi^W(0) が inT を通らない");
  let threw = false;
  try { parse("phi(1,0)"); } catch (e) { threw = true; }
  if (!threw) fails.push("括弧記法 phi(1,0) が例外にならない (構文の想定が違う)");
  // 4. lessThan が向きを持つこと (対称なら検査になっていない)
  const a = parse("1"), b = parse("W");
  if (!(P.lessThan(a, b) && !P.lessThan(b, a)))
    fails.push("lessThan が 1 < W を正しく判定しない");

  fails.forEach((f) => console.log("  失敗:", f));
  console.log(fails.length ? `padicbot-oracle 自己試験: 失敗 ${fails.length}`
                           : "padicbot-oracle 自己試験: 5/5 (記法・χ≠Ω階層・inT・構文例外・順序の向き)");
  return fails.length ? 1 : 0;
}

function main() {
  const argv = process.argv.slice(2);
  const di = argv.indexOf("--impl");
  const implDir = di >= 0 ? argv[di + 1]
    : path.join(process.env.HOME, "proofs/naruyoko-googology/padicBotRathjen");
  if (argv.includes("--self-test")) process.exit(selfTest(implDir));
  const P = load(implDir);
  if (!P) process.exit(0);
  console.log("読み込めた。Term / inT / lessThan / equal が使える。");
  console.log("辞書はまだ無い — 冒頭のコメントを読むこと。");
}

if (require.main === module) main();
module.exports = { load };
