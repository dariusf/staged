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
    anchor.style.fontSize = "1.2em"; // matching existing

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

document.addEventListener("DOMContentLoaded", buildTOC);
