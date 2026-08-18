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

const argv = process.argv.slice(2);
if (argv.length !== 1) {
  console.error("usage: bp2pss-ref.js \"<buchholz term>\"");
  process.exit(2);
}

try {
  ctx.clearTransMemos();
  const t = ctx.parseBuchholz(argv[0]);
  const M = ctx.TransRev(t);
  // writeCommon = true is the "(0,0)(1,1)" form; the default adds outer parens
  // and commas, which is not the form this repository's matrices are written in.
  console.log(ctx.stringifyPair(M, true));
} catch (e) {
  console.error("bp2pss-ref: " + e.message);
  process.exit(1);
}
