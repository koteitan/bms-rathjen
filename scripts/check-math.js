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
let bad = 0;
for (const f of process.argv.slice(2)) {
  const src = fs.readFileSync(f, "utf8");
  for (const m of src.matchAll(/\$`([^`]+)`\$/g))
    if (m[1].includes("\n")) { bad++; console.log(f, "MULTILINE INLINE:", JSON.stringify(m[1].slice(0, 60))); }
  const lines = src.split("\n"); let i = 0; const rest = [];
  while (i < lines.length) {
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
  const stray = j.replace(/\$`[^`]+`\$/g, "").match(/\$/g);
  if (stray) { bad += stray.length; console.log(f, "unprotected $ x" + stray.length); }
  const rows = src.match(/\\\\(?!\\)/g);
  if (rows) { bad += rows.length; console.log(f, "use \\cr not \\\\ x" + rows.length); }
}
console.log("errors:", bad);
process.exit(bad ? 1 : 0);
