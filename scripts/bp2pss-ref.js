#!/usr/bin/env node
"use strict";
/*
 * bp2pss-ref.js — the REFERENCE half of `scripts/bp2pss`.
 *
 * naruyoko's common.js has `TransRev(t)`, the inverse of `Trans`, defined (by its
 * own guard) on { t | t standard and t < D_1 0 }, i.e. t < Ω.  The reference CLI
 * `pss2bp.js` only wraps `Trans`, so this wrapper supplies the missing direction.
 *
 * common.js is NOT vendored into this repository -- this repo cites external
 * sources by URL, not by copy.  The file is loaded at run time out of $PSS2BP
 * (default $HOME/proofs/pss2bp) into a `vm` context, exactly the way pss2bp.js
 * does it: common.js is browser code with no DOM dependency whose top level is
 * only `function`/`var`, so every name lands on the context object.
 *
 *   node scripts/bp2pss-ref.js "D_0 D_1 0"        -> (0,0)(1,1)
 *   node scripts/bp2pss-ref.js "p0(p1(0))"        -> (0,0)(1,1)   ("p" is D in
 *                                                    common.js's parseBuchholz)
 *   node scripts/bp2pss-ref.js --batch            one term per line on stdin
 *   node scripts/bp2pss-ref.js --why "<term>"     which guard clause refuses it
 *   node scripts/bp2pss-ref.js --gindep "<term>"  does G use its level argument?
 *
 * --batch answers every line with `= <matrix>` or `! <why TransRev refused>` and
 * always exits 0; it is the form scripts/bp2pss-check.sh uses, matching the same
 * flag on bp2psscli so the two answer streams line up.
 *
 * Exit: 0 printed a matrix, 1 TransRev refused (outside its domain) or the term
 * did not parse, 2 common.js could not be loaded.
 */
const fs = require("fs");
const path = require("path");
const vm = require("vm");

const dir = process.env.PSS2BP || path.join(process.env.HOME || "", "proofs/pss2bp");
const commonPath = path.join(dir, "common.js");

let ctx;
try {
  const src = fs.readFileSync(commonPath, "utf8");
  ctx = {};
  vm.createContext(ctx);
  vm.runInContext(src, ctx, { filename: commonPath });
} catch (e) {
  console.error("bp2pss-ref: cannot load " + commonPath + ": " + e.message);
  process.exit(2);
}
if (typeof ctx.TransRev !== "function") {
  console.error("bp2pss-ref: " + commonPath + " has no TransRev");
  process.exit(2);
}

// writeCommon = true is the "(0,0)(1,1)" form; the default adds outer parens and
// commas, which is not the form this repository's matrices are written in.
function rev(s) {
  ctx.clearTransMemos();
  return ctx.stringifyPair(ctx.TransRev(ctx.parseBuchholz(s)), true);
}

const argv = process.argv.slice(2);

// Two diagnostics, used by scripts/bp2pss-check.sh to say WHICH of TransRev's two
// guard clauses refused a term.  They call common.js's own functions; nothing of
// its code is reproduced here.
if (argv.length === 2 && argv[0] === "--why") {
  const t = ctx.parseBuchholz(argv[1]);
  const omega = ctx.parseBuchholz("D_1 0");
  console.log("lt-omega=" + ctx.lessThanBuchholz(t, omega) +
              " std=" + ctx.isStandardBuchholz(t));
  process.exit(0);
}

// Is G's level argument used at all on a formal sum?  A level-sensitive G must
// answer differently for two different levels on (D_0 D_1 0, D_0 D_1 0).
if (argv.length === 2 && argv[0] === "--gindep") {
  const t = ctx.parseBuchholz(argv[1]);
  const f = (u) => "[" + ctx.G(t, u).map((e) => ctx.stringifyBuchholz(e, false)).join(",") + "]";
  console.log("G(t,0)=" + f(0) + " G(t,5)=" + f(5) + " same=" + (f(0) === f(5)));
  process.exit(0);
}

if (argv.length === 1 && argv[0] === "--batch") {
  const lines = fs.readFileSync(0, "utf8").split(/\r?\n/);
  for (const raw of lines) {
    const s = raw.trim();
    if (s === "" && raw === "") continue;      // trailing newline, not a case
    try {
      console.log("= " + rev(s));
    } catch (e) {
      console.log("! " + e.message);
    }
  }
  process.exit(0);
}

if (argv.length !== 1) {
  console.error("usage: bp2pss-ref.js \"<buchholz term>\"   |   bp2pss-ref.js --batch");
  process.exit(2);
}

try {
  console.log(rev(argv[0]));
} catch (e) {
  console.error("bp2pss-ref: " + e.message);
  process.exit(1);
}
