#!/usr/bin/env node
// Check the GitHub-rendered math of a Markdown file.
//
// Rendering locally proves nothing about GitHub: it transforms the math text on
// its way to the client-side renderer.  The safe forms (skill `github-math-check`):
//   display math -> ```math fence, never $$ ... $$
//   inline math  -> $`...`$, never bare $...$
//   never `\\` row breaks (GitHub turns them into `\\\`); use \cr
//   never `$` inside math, not even inside \text{} or a fence
//   INLINE MATH MUST NOT SPAN A LINE BREAK -- a $`...`$ broken across two lines
//     renders as literal text from the break onward.  Found on a published page
//     that every other check passed, because the checker's own regex matched
//     across newlines and so was blind to exactly the thing it was checking.
const katex = require(require("child_process")
  .execSync("npm root -g").toString().trim() + "/katex");
const fs = require("fs");
const path = require("path");
let bad = 0;
for (const f of process.argv.slice(2)) {
  const src = fs.readFileSync(f, "utf8");
  for (const m of src.matchAll(/\$`([^`]+)`\$/g))
    if (m[1].includes("\n")) { bad++; console.log(f, "MULTILINE INLINE:", JSON.stringify(m[1].slice(0, 60))); }
  const lines = src.split("\n"); let i = 0; const rest = [];
  while (i < lines.length) {
    // A plain ``` fence is literal text to GitHub -- no math is rendered inside
    // it, so its `$` must not be counted as unprotected.  Only ```math fences
    // are math.  (This check reported 3 false positives before the skip.)
    if (lines[i].trim().startsWith("```") && lines[i].trim() !== "```math") {
      let j = i + 1;
      while (j < lines.length && !lines[j].trim().startsWith("```")) j++;
      i = j + 1; continue;
    }
    if (lines[i].trim() === "```math") {
      let j = i + 1, body = [];
      while (j < lines.length && lines[j].trim() !== "```") body.push(lines[j++]);
      try { katex.renderToString(body.join("\n"), { displayMode: true, throwOnError: true }); }
      catch (e) { bad++; console.log(f, "DISPLAY L" + (i + 1) + ":", e.message.slice(0, 80)); }
      i = j + 1; continue;
    }
    rest.push(lines[i++]);
  }
  const j = rest.join("\n");
  for (const m of j.matchAll(/\$`([^`]+)`\$/g)) {
    try { katex.renderToString(m[1], { displayMode: false, throwOnError: true }); }
    catch (e) { bad++; console.log(f, "INLINE:", m[1].slice(0, 40), "|", e.message.slice(0, 60)); }
  }
  // Strip inline math first, THEN ordinary code spans: GitHub renders no math
  // inside `...`, so a `$` there is literal.  Counting it was a false positive.
  const stray = j.replace(/\$`[^`]+`\$/g, "").replace(/`[^`\n]*`/g, "").match(/\$/g);
  if (stray) { bad += stray.length; console.log(f, "unprotected $ x" + stray.length); }
  const rows = src.match(/\\\\(?!\\)/g);
  if (rows) { bad += rows.length; console.log(f, "use \\cr not \\\\ x" + rows.length); }
}

// ---- anchor check -------------------------------------------------------
// Headings drift; the in-page links pointing at them do not.  That happened
// three times in this repo, twice silently.  GitHub's rule, MEASURED against
// its own markdown API (POST https://api.github.com/markdown) rather than
// guessed: lowercase, drop everything that is not a letter/number (any script)
// or - _ or space, then spaces -> hyphens.  Note what that does to symbols:
// an emoji or an em-dash is REMOVED but the spaces around it are not, so
// "E.lim — ✅ の実体" yields "elim---の実体" with THREE hyphens.
function anchorOf(h) {
  return h.trim().toLowerCase()
    .replace(/[^\p{L}\p{N}\-_ ]/gu, "")
    .replace(/ /g, "-");
}

// self-test: if these ever fail, the rule drifted and every result below is
// worthless.  Each pair was read off GitHub's own rendering, not derived.
const ANCHOR_CASES = [
  ["E.zero / E.succ / E.lim — ✅ の実体", "ezero--esucc--elim---の実体"],
  ["✅ が検査していないもの",             "-が検査していないもの"],
  ["証明書の強さと、その限界",             "証明書の強さとその限界"],
  ["E.cofinal (展開と基本列の相互共終)",   "ecofinal-展開と基本列の相互共終"],
  ["E3 (展開と基本列の整合) — 本体のエビデンス", "e3-展開と基本列の整合--本体のエビデンス"],
  ["D.TM ($`\\mathfrak{T}(M)`$)",          "dtm-mathfraktm"],
  ["D.CertifiedIn / D.DomI",              "dcertifiedin--ddomi"],
];
for (const [h, want] of ANCHOR_CASES) {
  const got = anchorOf(h);
  if (got !== want) {
    bad++;
    console.log("ANCHOR RULE BROKEN: " + JSON.stringify(h) + " -> " + got + " want " + want);
  }
}

const anchorsOf = (src) => new Set(
  src.split("\n").filter(l => /^#{1,6}\s/.test(l))
     .map(l => anchorOf(l.replace(/^#{1,6}\s*/, ""))));

for (const f of process.argv.slice(2)) {
  const src = fs.readFileSync(f, "utf8");
  const here = anchorsOf(src);
  for (const m of src.matchAll(/\]\(([^)\s]*?)#([^)\s]+)\)/g)) {
    const [tgt, anc] = [m[1], m[2]];
    let target = here;
    if (tgt) {
      const q = path.normalize(path.join(path.dirname(f), tgt));
      if (!fs.existsSync(q)) { bad++; console.log(f, "LINK TARGET MISSING:", tgt); continue; }
      // `file.lean#L237` is a GitHub line link, not a heading anchor.  Only
      // Markdown targets have headings to check against.
      if (!q.endsWith(".md")) continue;
      target = anchorsOf(fs.readFileSync(q, "utf8"));
    }
    if (!target.has(anc)) {
      bad++;
      console.log(f, "DEAD ANCHOR:", (tgt || "") + "#" + anc);
    }
  }
}

console.log("errors:", bad);
process.exit(bad ? 1 : 0);
