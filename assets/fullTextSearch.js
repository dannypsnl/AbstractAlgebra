let sourcemap = [];

fetch("/sourcemap.json")
  .then(value => value.json())
  .then(sm => {
      sourcemap = sm;
  })
  .catch((_) => console.log("You're not in local development environment"));

function trim(str, ch) {
  var start = 0,
    end = str.length;
  while (start < end && str[start] === ch) ++start;
  while (end > start && str[end - 1] === ch) --end;
  return start > 0 || end < str.length ? str.substring(start, end) : str;
}

document.addEventListener(
  "keydown",
  (event) => {
    const keyName = event.key;

    if (keyName === "Control" || keyName === "Meta") {
      return;
    }

    if ((event.metaKey || event.ctrlKey) && keyName === "e") {
      let addr =
        document.location.pathname === "/"
          ? "index"
          : trim(document.location.pathname, "/");
      window.open(`vscode://file${sourcemap[addr]}`);
    }
  },
  false
);

const searchBar = input({
  type: "text",
  id: "search-bar",
  spellcheck: false,
  autocomplete: "off",
  placeholder: "Type title or ID to search……",
});
const searchResult = div({ id: "search-result" });
const searchDialog = dialog(
  { id: "search-dialog" },
  div(
    { className: "search-header" },
    a({ className: "search-home", href: "/", title: "Home" }, "⌂ Home"),
    searchBar
  ),
  searchResult,
  div(
    { className: "search-footer" },
    span(kbd("↑"), kbd("↓"), " Move"),
    span(kbd("↵"), " Open"),
    span(kbd("esc"), " Close")
  )
);
document.body.prepend(searchDialog);

let cards = [];
let pagefind = null;
let loading = null;

function loadSearch() {
  if (loading) return loading;
  loading = Promise.all([
    fetch("/cards.json")
      .then((r) => r.json())
      .then((list) => {
        cards = list;
      })
      .catch((err) => console.error("failed to load /cards.json", err)),
    import("/pagefind/pagefind.js")
      .then(async (mod) => {
        await mod.init();
        pagefind = mod;
      })
      .catch((err) => console.warn("pagefind unavailable, title-only search", err)),
  ]);
  return loading;
}

function addrOf(url) {
  const addr = trim(url.split(/[?#]/)[0], "/");
  return addr === "" ? "index" : addr;
}

function createResultItem(obj) {
  const href = obj.id === "index" ? "/" : `/${obj.id}`;

  const titleSpan = span({ className: "sr-title" });
  titleSpan.innerHTML = obj.title || `${obj.id}`;

  const line = [];
  if (obj.taxon) {
    line.push(span({ className: "sr-taxon" }, `${obj.taxon}.`));
  }
  line.push(titleSpan);
  line.push(span({ className: "sr-id" }, `[${obj.id}]`));

  const children = [span({ className: "sr-line" }, ...line)];
  if (obj.excerpt) {
    const excerpt = span({ className: "sr-excerpt" });
    excerpt.innerHTML = obj.excerpt;
    children.push(excerpt);
  }

  return a({ className: "search-result-item", href }, ...children);
}

let resultItems = [];
let selectedIndex = -1;

function renderResults(list) {
  searchResult.innerHTML = "";
  resultItems = [];

  if (list.length === 0) {
    searchResult.appendChild(div({ className: "search-empty" }, "No result"));
    selectedIndex = -1;
    return;
  }

  for (const obj of list) {
    const el = createResultItem(obj);
    searchResult.appendChild(el);
    resultItems.push(el);
  }
  setSelected(0);
}

function setSelected(i) {
  if (resultItems.length === 0) {
    selectedIndex = -1;
    return;
  }
  selectedIndex = ((i % resultItems.length) + resultItems.length) % resultItems.length;
  resultItems.forEach((el, idx) => {
    el.classList.toggle("selected", idx === selectedIndex);
  });
  resultItems[selectedIndex].scrollIntoView({ block: "nearest" });
}

searchResult.addEventListener("mousemove", (evt) => {
  const item = evt.target.closest(".search-result-item");
  if (!item) return;
  const idx = resultItems.indexOf(item);
  if (idx >= 0 && idx !== selectedIndex) {
    setSelected(idx);
  }
});

const FULL_TEXT_LIMIT = 25;

function relevanceFilter(query) {
  const needle = query.toLowerCase();
  const terms = query.split(/\s+/).filter((t) => t.length >= 2).map((t) => t.toLowerCase());
  return (excerpt) => {
    const text = (excerpt || "").replace(/<[^>]*>/g, "").toLowerCase();
    return text.includes(needle) || terms.some((t) => text.includes(t));
  };
}

let querySeq = 0;

async function runQuery(query) {
  const seq = ++querySeq;
  await loadSearch();
  if (seq !== querySeq) return;

  const q = query.trim();
  if (!q) {
    renderResults(cards);
    return;
  }

  const needle = q.toLowerCase();
  const byTitle = cards.filter(
    (c) =>
      c.id.toLowerCase().includes(needle) ||
      (c.plain || "").toLowerCase().includes(needle)
  );
  renderResults(byTitle);

  if (!pagefind) return;

  const found = await pagefind.debouncedSearch(q, {}, 120);
  if (found === null || seq !== querySeq) return;

  const known = new Set(byTitle.map((c) => c.id));
  const byId = new Map(cards.map((c) => [c.id, c]));
  const results = await Promise.all(
    found.results.slice(0, FULL_TEXT_LIMIT).map((r) => r.data())
  );
  if (seq !== querySeq) return;

  const relevant = relevanceFilter(q);
  const merged = byTitle.slice();
  for (const data of results) {
    const id = addrOf(data.url);
    if (known.has(id) || !relevant(data.excerpt)) continue;
    known.add(id);
    const card = byId.get(id);
    merged.push({
      id,
      title: card?.title ?? data.meta?.title ?? id,
      taxon: card?.taxon ?? data.meta?.taxon,
      excerpt: data.excerpt,
    });
  }
  renderResults(merged);
}

let dialogOpen = false;
function setDialog(open) {
  if (open) {
    searchDialog.showModal();
    dialogOpen = true;
    $("#whole").classList.add("blur");
    searchBar.focus();
    searchBar.select();
    runQuery(searchBar.value);
  } else {
    searchDialog.close();
  }
}

searchDialog.addEventListener("close", () => {
  dialogOpen = false;
  $("#whole").classList.remove("blur");
});

let composing = false;
let compositionEndedAt = 0;
const COMPOSITION_ESCAPE_MS = 150;

searchDialog.addEventListener("cancel", (evt) => {
  if (composing || Date.now() - compositionEndedAt < COMPOSITION_ESCAPE_MS) {
    evt.preventDefault();
  }
});

document.addEventListener(
  "keydown",
  (event) => {
    const keyName = event.key;

    if (keyName === "Control" || keyName === "Meta") {
      return;
    }

    if ((event.metaKey || event.ctrlKey) && keyName === "k") {
      setDialog(!dialogOpen);
    }
  },
  false
);

const isComposing = (evt) => evt.isComposing || evt.keyCode === 229;

let lastQueried = null;
function queryFromInput(value) {
  if (value === lastQueried) return;
  lastQueried = value;
  runQuery(value);
}

searchBar.addEventListener(
  "input",
  function (evt) {
    if (isComposing(evt)) return;
    queryFromInput(evt.target.value);
  },
  false
);

searchBar.addEventListener("compositionstart", function () {
  composing = true;
});

searchBar.addEventListener("compositionend", function (evt) {
  composing = false;
  compositionEndedAt = Date.now();
  queryFromInput(evt.target.value);
});

searchBar.addEventListener("keydown", function (evt) {
  if (isComposing(evt)) return;

  switch (evt.key) {
    case "ArrowDown":
      evt.preventDefault();
      setSelected(selectedIndex + 1);
      break;
    case "ArrowUp":
      evt.preventDefault();
      setSelected(selectedIndex - 1);
      break;
    case "Enter":
      if (selectedIndex >= 0 && resultItems[selectedIndex]) {
        evt.preventDefault();
        window.location.assign(resultItems[selectedIndex].href);
      }
      break;
  }
});
