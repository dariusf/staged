const FONT_SIZE = "1.2em"; // matching existing

function nodesWithTextAndClass(text, cls) {
  const xpathExpression = `//*[contains(text(), '${text}') and contains(@class, '${cls}')]`;
  const xpathResult = document.evaluate(
    xpathExpression,
    document,
    null,
    XPathResult.ORDERED_NODE_SNAPSHOT_TYPE,
    null
  );
  let nodes = [];
  for (let i = 0; i < xpathResult.snapshotLength; i++) {
    nodes.push(xpathResult.snapshotItem(i));
  }
  return nodes;
}

function buildTOC() {
  const headers = document.querySelectorAll("h1:not(.title)");

  if (headers.length === 0) return;

  const tocDiv = document.createElement("div");
  tocDiv.style.maxWidth = "fit-content";
  tocDiv.style.margin = "0 auto";

  const tocList = document.createElement("ul");

  headers.forEach((header, index) => {
    const anchor = document.createElement("a");
    const headerID = `header-${index}`;
    anchor.setAttribute("href", `#${headerID}`);
    anchor.textContent = header.textContent;
    anchor.style.fontSize = FONT_SIZE;

    header.setAttribute("id", headerID);

    const listItem = document.createElement("li");
    listItem.appendChild(anchor);

    tocList.appendChild(listItem);
  });

  tocDiv.appendChild(tocList);

  document.body.insertBefore(
    document.createElement("hr"),
    document.querySelector(".title").nextSibling
  );
  document.body.insertBefore(
    tocDiv,
    document.querySelector(".title").nextSibling
  );
  document.body.insertBefore(
    document.createElement("hr"),
    document.querySelector(".title").nextSibling
  );
}

function buildLemmaIndex() {
  let index = document.createElement("div");
  let lemmas = nodesWithTextAndClass("Lemma", "kwd");

  const list = document.createElement("ul");
  const hdr = document.createElement("h1");
  hdr.textContent = "Lemma Index";
  index.appendChild(hdr);
  index.appendChild(list);
  lemmas.forEach((lem, index) => {
    const anchor = document.createElement("a");
    const id = `lem-${index}`;
    anchor.setAttribute("href", `#${id}`);
    anchor.textContent = `Lemma ${lem.nextSibling.nextSibling.textContent}`;
    anchor.style.fontSize = FONT_SIZE;

    lem.setAttribute("id", id);

    const listItem = document.createElement("li");
    listItem.appendChild(anchor);

    list.appendChild(listItem);
  });

  document.body.insertBefore(index, document.querySelector(".footer"));
}
function mungeDocument() {
  buildLemmaIndex();
  buildTOC();
}

document.addEventListener("DOMContentLoaded", mungeDocument);
