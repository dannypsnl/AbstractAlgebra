// Build the Pagefind index from tr's per-card metadata.
//
// Not `pagefind --site _build`: this site transcludes, so a card's text also
// appears in index.html, in every parent card's page and in its own, and
// crawling the HTML would index the same passage several times over while the
// huge pages drown out the real cards. `raco tr meta --all` emits one record
// per card, so the index unit matches the site's own unit of meaning.
//
// Usage: node build-search-index.mjs [output-dir]   (default _build)
import * as pagefind from "pagefind";
import { rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { join } from "node:path";

const outDir = process.argv[2] ?? "_build";

const entities = { amp: "&", lt: "<", gt: ">", quot: '"', apos: "'", nbsp: " " };
const decodeEntities = (s) =>
  s.replace(/&(#x[0-9a-fA-F]+|#\d+|[a-zA-Z]+);/g, (whole, body) => {
    if (body[0] === "#") {
      const code = body[1] === "x" ? parseInt(body.slice(2), 16) : parseInt(body.slice(1), 10);
      return Number.isNaN(code) ? whole : String.fromCodePoint(code);
    }
    return entities[body] ?? whole;
  });

const titleToText = (segments) =>
  segments
    .map((seg) => {
      if (typeof seg !== "string") return "";
      if (!seg.includes("<")) return seg;
      const tex = [...seg.matchAll(/<annotation encoding="application\/x-tex">([\s\S]*?)<\/annotation>/g)]
        .map((m) => decodeEntities(m[1]))
        .join(" ");
      return tex || decodeEntities(seg.replace(/<[^>]*>/g, ""));
    })
    .join("")
    .replace(/\s+/g, " ")
    .trim();

const allDocs = JSON.parse(execFileSync("raco", ["tr", "meta", "--all"], { encoding: "utf8" }));
if (allDocs.length === 0) {
  throw new Error("raco tr meta --all returned no cards — did tr build run?");
}

// The metadata store is cumulative: tr writes an addr's metadata once and never
// deletes it, so a card later excluded from the build would otherwise leak into
// every index from then on. A card's own output directory exists only for the
// addrs actually built this run, which makes it the authoritative membership
// check.
const cardOutputPath = (id) => (id === "index" ? join(outDir, "index.html") : join(outDir, id, "index.html"));
const docs = allDocs.filter((doc) => existsSync(cardOutputPath(doc.id)));
if (docs.length < allDocs.length) {
  console.log(`pagefind: skipped ${allDocs.length - docs.length} card(s) not built into ${outDir}`);
}

const LANGUAGE = "en";

const { index } = await pagefind.createIndex({ forceLanguage: LANGUAGE });

await rm(join(outDir, "pagefind"), { recursive: true, force: true });

const cards = [];
for (const doc of docs) {
  const segments = Array.isArray(doc.title) ? doc.title : [];
  const titleHtml = segments.filter((s) => typeof s === "string").join("");
  const titleText = titleToText(segments) || doc.id;
  const text = typeof doc.text === "string" ? doc.text : "";

  cards.push({
    id: doc.id,
    title: titleHtml || doc.id,
    plain: titleText,
    ...(doc.taxon ? { taxon: doc.taxon } : {}),
  });

  const meta = { title: titleText };
  if (doc.taxon) meta.taxon = doc.taxon;
  if (doc.date) meta.date = String(doc.date);

  await index.addCustomRecord({
    url: doc.id === "index" ? "/" : `/${doc.id}`,
    content: `${titleText}\n${text}`,
    language: LANGUAGE,
    meta,
  });
}

const { page_count } = await index.writeFiles({ outputPath: join(outDir, "pagefind") });
await pagefind.close();

for (const junk of [
  "pagefind-ui.js",
  "pagefind-ui.css",
  "pagefind-modular-ui.js",
  "pagefind-modular-ui.css",
  "pagefind-component-ui.js",
  "pagefind-component-ui.css",
  "pagefind-highlight.js",
]) {
  await rm(join(outDir, "pagefind", junk), { force: true });
}

await writeFile(join(outDir, "cards.json"), JSON.stringify(cards));

console.log(`pagefind: indexed ${page_count ?? cards.length} cards into ${outDir}/pagefind`);
