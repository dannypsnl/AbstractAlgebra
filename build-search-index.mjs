import * as pagefind from "pagefind";
import { readFile, readdir, rm, writeFile } from "node:fs/promises";
import { join } from "node:path";

const outDir = process.argv[2] ?? "_build";
const tmpDir = process.argv[3] ?? "_tmp";

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

const metaFiles = (await readdir(tmpDir, { recursive: true }))
  .filter((f) => f.endsWith(".metadata.json"))
  .sort();
const docs = await Promise.all(
  metaFiles.map(async (f) => JSON.parse(await readFile(join(tmpDir, f), "utf8")))
);
if (docs.length === 0) {
  throw new Error(`no *.metadata.json under ${tmpDir}/ — did tr build run?`);
}

const LANGUAGE = "zh";

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
