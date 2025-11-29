let sourcemap = [];

fetch("/sourcemap.json")
  .then((value) => {
    value.json().then((sm) => {
      sourcemap = sm;
    });
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

// `MiniSearch` is already in global
window.miniSearch = new MiniSearch({
  fields: ["taxon", "title", "text"], // fields to index for full-text search
  storeFields: ["taxon", "title"], // fields to return with search results
});

let allDocuments = [];

fetch("/search.json")
  .then((value) => {
    value.json().then((documents) => {
      allDocuments = documents;
      window.miniSearch.addAll(documents);
      displayAllResults();
    });
  })
  .catch((err) => console.error(err));

function createResultSpan(obj) {
  const href = obj.id === "index" ? "/" : `/${obj.id}`;
  const linkElement = a({ href });

  for (let i = 0; i < obj.title.length; i++) {
    linkElement.innerHTML += obj.title[i];
  }
  if (!obj.title || obj.title.length === 0) {
    linkElement.innerHTML += `${obj.id}`;
  }
                                                                                                          │

  return span({}, `[${obj.id}] `, linkElement);
}

function displayAllResults() {
  const search_result = $("#search-result");
  search_result.innerHTML = "";
  for (const obj of allDocuments) {
    search_result.appendChild(createResultSpan(obj));
    search_result.appendChild(br({}));
  }
}

let dialogOpen = false;
document.addEventListener(
  "keydown",
  (event) => {
    const keyName = event.key;

    if (keyName === "Control" || keyName === "Meta") {
      return;
    }

    if ((event.metaKey || event.ctrlKey) && keyName === "k") {
      const dialog = $("#search-dialog");
      if (dialogOpen) {
        $("#whole").classList.remove("blur");
        dialog.close();
        dialogOpen = !dialogOpen;
      } else {
        dialog.showModal();
        dialogOpen = !dialogOpen;
        $("#whole").classList.add("blur");
      }
    }
  },
  false
);

const input = $("#search-bar");
input.addEventListener(
  "input",
  function (evt) {
    if (!evt.target.value.trim()) {
      displayAllResults();
      return;
    }

    let results = window.miniSearch.search(evt.target.value, {
      fields: ["taxon", "title", "text"],
      prefix: true,
    });

    const search_result = $("#search-result");
    search_result.innerHTML = "";
    for (const obj of results) {
      search_result.appendChild(createResultSpan(obj));
      search_result.appendChild(br({}));
    }
  },
  false
);
