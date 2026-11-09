// MathFin documentation site: theme, search, math, graphs, chart tooltips.
(() => {
  const base = document.body.dataset.base || "";
  const css = (v) => getComputedStyle(document.documentElement).getPropertyValue(v).trim();

  // ---------------------------------------------------------------- theme
  const themeBtn = document.getElementById("theme");
  try {
    const saved = localStorage.getItem("mf-theme");
    if (saved) document.documentElement.dataset.theme = saved;
  } catch (_) {}
  const graphs = [];
  if (themeBtn) themeBtn.addEventListener("click", () => {
    const dark = matchMedia("(prefers-color-scheme: dark)").matches;
    const cur = document.documentElement.dataset.theme || (dark ? "dark" : "light");
    const next = cur === "dark" ? "light" : "dark";
    document.documentElement.dataset.theme = next;
    try { localStorage.setItem("mf-theme", next); } catch (_) {}
    graphs.forEach((g) => g.restyle());
  });

  // ---------------------------------------------------------------- math
  const renderMath = (el) => {
    if (window.renderMathInElement) {
      renderMathInElement(el, {
        delimiters: [{ left: "$$", right: "$$", display: true }, { left: "$", right: "$", display: false }],
        throwOnError: false, ignoredTags: ["script", "noscript", "style", "textarea", "pre", "code"],
      });
    }
  };
  const mathReady = () => document.querySelectorAll("[data-math]").forEach(renderMath);
  if (document.readyState === "complete") mathReady(); else addEventListener("load", mathReady);

  // ---------------------------------------------------------------- search
  const box = document.getElementById("q");
  const out = document.getElementById("results");
  let rows = null, sel = -1, hits = [];
  const load = async () => rows || (rows = await (await fetch(base + "search.json")).json());
  const score = (r, terms, raw) => {
    const n = r.n.toLowerCase(), short = n.slice(n.lastIndexOf(".") + 1);
    let s = 0;
    for (const t of terms) {
      if (!r.h.includes(t)) return -1;
      if (short === t) s += 100; else if (short.startsWith(t)) s += 40;
      else if (n.includes(t)) s += 20; else s += 2;
    }
    if (short === raw) s += 200;
    if (r.k === "theorem" || r.k === "def" || r.k === "structure") s += 3;
    return s - n.length / 200;
  };
  const show = () => {
    out.innerHTML = "";
    hits.forEach((r, i) => {
      const a = document.createElement("a");
      a.href = base + r.u; if (i === sel) a.className = "sel";
      const nm = document.createElement("div"); nm.className = "r-name"; nm.textContent = r.n;
      const md = document.createElement("div"); md.className = "r-mod"; md.textContent = r.k + " · " + r.m;
      a.append(nm, md);
      if (r.d) { const dd = document.createElement("div"); dd.className = "r-doc"; dd.textContent = r.d; a.append(dd); }
      out.append(a);
    });
    out.classList.toggle("open", hits.length > 0);
  };
  if (box && out) {
    box.addEventListener("input", async () => {
      const raw = box.value.trim().toLowerCase();
      const terms = raw.split(/\s+/).filter(Boolean);
      if (!terms.length) { hits = []; show(); return; }
      const all = await load();
      hits = all.map((r) => [score(r, terms, raw), r]).filter(([s]) => s >= 0)
        .sort((a, b) => b[0] - a[0]).slice(0, 40).map(([, r]) => r);
      sel = hits.length ? 0 : -1; show();
    });
    box.addEventListener("keydown", (e) => {
      if (e.key === "ArrowDown") { sel = Math.min(sel + 1, hits.length - 1); show(); e.preventDefault(); }
      else if (e.key === "ArrowUp") { sel = Math.max(sel - 1, 0); show(); e.preventDefault(); }
      else if (e.key === "Enter" && hits[sel]) { location.href = base + hits[sel].u; }
      else if (e.key === "Escape") { box.blur(); out.classList.remove("open"); }
    });
    document.addEventListener("keydown", (e) => {
      if (e.key === "/" && document.activeElement !== box && !/input|textarea/i.test(document.activeElement.tagName)) {
        box.focus(); e.preventDefault();
      }
    });
    document.addEventListener("click", (e) => { if (!e.target.closest(".search")) out.classList.remove("open"); });
  }

  // ---------------------------------------------------------------- tooltips
  const tip = document.createElement("div"); tip.className = "tip"; document.body.append(tip);
  const moveTip = (x, y) => {
    const w = tip.offsetWidth, h = tip.offsetHeight;
    tip.style.left = Math.min(x + 14, innerWidth - w - 8) + scrollX + "px";
    tip.style.top = Math.min(y + 14, innerHeight - h - 8) + scrollY + "px";
  };
  const showTip = (htmlText, x, y) => { tip.innerHTML = htmlText; tip.style.display = "block"; moveTip(x, y); };
  const hideTip = () => { tip.style.display = "none"; };
  document.querySelectorAll("[data-tip]").forEach((el) => {
    el.addEventListener("mousemove", (e) => showTip(el.dataset.tip, e.clientX, e.clientY));
    el.addEventListener("mouseleave", hideTip);
  });

  // ---------------------------------------------------------------- graphs
  if (!window.cytoscape) return;
  if (window.cytoscapeDagre) cytoscape.use(cytoscapeDagre);
  const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));

  const palette = () => ({
    ink: css("--ink"), ink2: css("--ink-2"), muted: css("--muted"), line: css("--line"), axis: css("--axis"),
    surface: css("--surface"), s1: css("--s1"), s2: css("--s2"), s3: css("--s3"), good: css("--good"),
    accent: css("--accent"),
  });
  const layerColor = (p, layer) => ({ roots: p.s1, trunk: p.s2, limbs: p.s3 }[layer] || p.muted);

  const styleFor = (kind, p) => {
    const common = [
      { selector: "node", style: {
          "label": "data(label)", "color": p.ink, "font-family": "system-ui, -apple-system, Segoe UI, sans-serif",
          "font-size": 11, "text-wrap": "wrap", "text-max-width": 150, "text-valign": "bottom", "text-margin-y": 5,
          "background-color": p.muted, "border-width": 2, "border-color": p.surface, "width": 14, "height": 14,
          "min-zoomed-font-size": 6 } },
      { selector: "edge", style: {
          "width": 1, "line-color": p.axis, "target-arrow-color": p.axis, "target-arrow-shape": "triangle",
          "arrow-scale": 0.7, "curve-style": "bezier", "opacity": 0.8 } },
      { selector: ".faded", style: { "opacity": 0.12 } },
      { selector: "node.hi", style: { "border-color": p.ink, "border-width": 2.5 } },
      { selector: "edge.hi", style: { "line-color": p.ink2, "target-arrow-color": p.ink2, "opacity": 1, "width": 2 } },
    ];
    if (kind === "map") return common.concat([
      { selector: "node", style: {
          "width": "data(sz)", "height": "data(sz)", "background-color": (n) => layerColor(p, n.data("layer")),
          "font-size": 14, "font-weight": 600, "text-valign": "bottom", "text-margin-y": 6,
          "text-background-color": p.surface, "text-background-opacity": 0.85, "text-background-padding": 2,
          "text-background-shape": "round-rectangle", "text-max-width": 140 } },
      { selector: "edge", style: { "width": "data(ew)", "curve-style": "bezier", "opacity": 0.45,
          "arrow-scale": 0.7 } },
    ]);
    const wFor = (n) => Math.min(String(n.data("label")).length * 6.6, 150) + 20;
    const hFor = (n) => Math.ceil(String(n.data("label")).length * 6.6 / 150) * 15 + 14;
    return common.concat([
      { selector: "node", style: { "shape": "round-rectangle", "width": wFor, "height": hFor,
          "text-valign": "center", "text-halign": "center", "text-margin-y": 0, "text-max-width": 150,
          "background-color": p.surface, "border-color": p.axis, "border-width": 1.5, "font-size": 11.5,
          "min-zoomed-font-size": 4 } },
      { selector: "node.proved", style: { "border-color": p.good, "border-width": 2 } },
      { selector: "node.upstream", style: { "border-color": p.s1, "border-width": 2 } },
      { selector: "node.frontier", style: { "border-style": "dashed", "border-color": p.muted, "color": p.ink2 } },
      { selector: "node.center", style: { "background-color": p.accent, "color": p.surface, "border-color": p.accent,
          "font-weight": 600 } },
      { selector: "node.roots", style: { "border-color": p.s1, "border-width": 2 } },
      { selector: "node.trunk", style: { "border-color": p.s2, "border-width": 2 } },
      { selector: "node.limbs", style: { "border-color": p.s3, "border-width": 2 } },
      { selector: "edge", style: { "curve-style": "bezier", "arrow-scale": 0.6 } },
    ]);
  };

  document.querySelectorAll("[data-graph]").forEach((el) => {
    const spec = JSON.parse(document.getElementById(el.dataset.graph).textContent);
    const kind = spec.kind || "dag";
    const p0 = palette();
    const elements = spec.nodes.map((n) => ({ data: n, classes: n.cls || "" }))
      .concat(spec.edges.map((e, i) => ({ data: Object.assign({ id: "e" + i }, e), classes: e.cls || "" })));
    const ring = { roots: 3, trunk: 2, limbs: 1 };
    const layout = kind === "map"
      ? { name: "concentric", animate: false, padding: 30, minNodeSpacing: 34, startAngle: 3.4,
          concentric: (n) => ring[n.data("layer")] || 1, levelWidth: () => 1, avoidOverlap: true }
      : { name: window.cytoscapeDagre ? "dagre" : "breadthfirst", rankDir: spec.rankDir || "LR",
          nodeSep: 10, rankSep: 56, edgeSep: 6, padding: 20, directed: true };
    const cy = cytoscape({ container: el, elements, style: styleFor(kind, p0), layout,
      minZoom: 0.15, maxZoom: 3, boxSelectionEnabled: false });
    graphs.push({ restyle: () => cy.style(styleFor(kind, palette())) });

    // a layered graph gets the height that shows it at a readable scale, not a fixed box
    const fitBox = () => {
      if (kind !== "map") {
        const bb = cy.elements().boundingBox();
        const z = Math.min(1, (el.clientWidth - 40) / Math.max(bb.w, 1));
        el.style.height = Math.round(Math.max(180, Math.min(1500, bb.h * z + 60))) + "px";
        cy.resize();
      }
      cy.fit(undefined, 24);
      if (cy.zoom() > 1.1) { cy.zoom(1.1); cy.center(); }
    };
    fitBox();

    // hover: neighbourhood highlight + tooltip
    cy.on("mouseover", "node", (e) => {
      const n = e.target, hood = n.closedNeighborhood();
      cy.elements().not(hood).addClass("faded"); hood.addClass("hi");
      const d = n.data();
      const lines = [`<b>${esc(d.full || d.label)}</b>`];
      if (d.info) lines.push(esc(d.info));
      const oe = e.originalEvent; if (oe) showTip(lines.join("<br>"), oe.clientX, oe.clientY);
      el.style.cursor = d.url || spec.panel ? "pointer" : "default";
    });
    cy.on("mousemove", "node", (e) => { const oe = e.originalEvent; if (oe) moveTip(oe.clientX, oe.clientY); });
    cy.on("mouseout", "node", () => { cy.elements().removeClass("faded hi"); hideTip(); el.style.cursor = "default"; });
    cy.on("tap", "node", (e) => {
      const d = e.target.data();
      if (spec.panel) {
        const side = document.getElementById(spec.panel);
        const card = document.getElementById("bp-" + d.id);
        if (side && card) {
          side.innerHTML = card.innerHTML; renderMath(side);
          side.scrollIntoView({ block: "nearest", behavior: "smooth" }); return;
        }
      }
      if (d.url) location.href = base + d.url;
    });

    // tools
    const tools = document.createElement("div"); tools.className = "graph-tools";
    const fit = document.createElement("button"); fit.textContent = "fit"; fit.onclick = fitBox;
    tools.append(fit); el.append(tools);
  });
})();
