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

function createResultItem(obj) {
  const href = obj.id === "index" ? "/" : `/${obj.id}`;

  const titleSpan = span({ className: "sr-title" });
  const title = Array.isArray(obj.title) ? obj.title.join("") : obj.title || "";
  titleSpan.innerHTML = title || `${obj.id}`;

  const children = [span({ className: "sr-id" }, `[${obj.id}]`)];
  if (obj.taxon) {
    children.push(span({ className: "sr-taxon" }, obj.taxon));
  }
  children.push(titleSpan);

  return a({ className: "search-result-item", href }, ...children);
}

// 目前畫面上的結果項目與被選取的 index
let resultItems = [];
let selectedIndex = -1;

function renderResults(list) {
  const search_result = $("#search-result");
  search_result.innerHTML = "";
  resultItems = [];

  if (list.length === 0) {
    search_result.appendChild(div({ className: "search-empty" }, "沒有符合的結果"));
    selectedIndex = -1;
    return;
  }

  for (const obj of list) {
    const el = createResultItem(obj);
    search_result.appendChild(el);
    resultItems.push(el);
  }
  setSelected(0);
}

function setSelected(i) {
  if (resultItems.length === 0) {
    selectedIndex = -1;
    return;
  }
  // wrap-around：往上超過頭跳到尾、往下超過尾跳回頭
  selectedIndex = ((i % resultItems.length) + resultItems.length) % resultItems.length;
  resultItems.forEach((el, idx) => {
    el.classList.toggle("selected", idx === selectedIndex);
  });
  resultItems[selectedIndex].scrollIntoView({ block: "nearest" });
}

// 鍵盤與滑鼠共用同一個 selectedIndex
$("#search-result").addEventListener("mousemove", (evt) => {
  const item = evt.target.closest(".search-result-item");
  if (!item) return;
  const idx = resultItems.indexOf(item);
  if (idx >= 0 && idx !== selectedIndex) {
    setSelected(idx);
  }
});

function displayAllResults() {
  renderResults(allDocuments);
}

let dialogOpen = false;
function setDialog(dialog, open) {
  if (open) {
    dialog.showModal();
    dialogOpen = true;
    $("#whole").classList.add("blur");
    // 開啟後把鍵盤 focus 放到搜尋輸入框
    const bar = $("#search-bar");
    bar.focus();
    bar.select();
  } else {
    // 只要呼叫 close()，dialog 的 "close" 事件會統一做善後
    dialog.close();
  }
}

// Esc / backdrop / .close() 任何關閉方式都會走這裡，狀態不會失同步
$("#search-dialog").addEventListener("close", () => {
  dialogOpen = false;
  $("#whole").classList.remove("blur");
});

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
        setDialog(dialog, false);
      } else {
        setDialog(dialog, true);
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

    const results = window.miniSearch.search(evt.target.value, {
      fields: ["taxon", "title", "text"],
      prefix: true,
    });
    renderResults(results);
  },
  false
);

// 方向鍵在結果間移動、Enter 前往目前選取的項目
input.addEventListener("keydown", function (evt) {
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
