/* The program tree (tree.html): the blueprint drawn as a tree, with the corpus as its leaves.
   Data: the JSON block #tree-data, written by tools/verify/docs_site.py from program_tree.tree_data.
   Needs d3 (loaded by the page). */
(function () {
  "use strict";
  const el = document.getElementById("tree-data");
  if (!el || !window.d3) return;
  const DATA = JSON.parse(el.textContent);
  const GH = DATA.repo + "/issues/";
  const N = new Map(DATA.nodes.map(n => [n.l, n]));
  const esc = s => String(s ?? "").replace(/[&<>"]/g, c => ({"&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;"}[c]));
  const wood = n => n.s !== "frontier";

  // depth: one above the deepest node used
  const memo = new Map();
  function depth(l, seen = new Set()) {
    if (memo.has(l)) return memo.get(l);
    const n = N.get(l); if (!n || seen.has(l)) return 0;
    seen.add(l);
    const us = n.u.filter(u => N.has(u));
    const d = us.length ? 1 + Math.max(...us.map(u => depth(u, seen))) : 0;
    memo.set(l, d); return d;
  }
  for (const n of DATA.nodes) {
    n.dep = depth(n.l);
    n.partial = n.s === "frontier" && (n.core || []).length > 0;
    n.open = (n.i || []).filter(x => x[1] === "o" && !x[2]);
  }
  // each node hangs from its deepest use; the other uses are drawn on demand
  function parentOf(n) {
    const us = n.u.filter(u => N.has(u)).map(u => N.get(u));
    if (!us.length) return n.s === "upstream" || n.ground ? "ground" : "limb:" + n.a;
    us.sort((a, b) => (b.dep - a.dep) || (wood(b) - wood(a)) || a.l.localeCompare(b.l));
    return us[0].l;
  }
  const LIMBS = ["actuarial", "risk", "portfolio", "execution", "defi", "credit", "fx", "fixed-income",
    "foundations", "black-scholes", "stoch-vol", "binomial", "futures", "contracts", "commodities"];
  const rank = a => { const i = LIMBS.indexOf(a); return i < 0 ? 99 : i; };
  const rows = [{id: "ground"}], limbs = new Set();
  for (const n of DATA.nodes) { const p = parentOf(n); if (p.startsWith("limb:")) limbs.add(n.a); rows.push({id: n.l, parentId: p, node: n}); }
  for (const a of limbs) rows.push({id: "limb:" + a, parentId: "ground", limb: a});
  const root = d3.stratify().id(d => d.id).parentId(d => d.parentId)(rows);
  root.each(d => { d.w = 1 + (d.data.node ? d.data.node.e : 0); });
  root.eachAfter(d => { if (d.children) d.w += d3.sum(d.children, c => c.w); });
  const key = d => d.data.limb ?? d.data.node?.a ?? "";
  root.sort((a, b) => (rank(key(a)) - rank(key(b))) || ((a.data.node?.dep ?? 0) - (b.data.node?.dep ?? 0)) || a.id.localeCompare(b.id));

  // geometry: a canopy over the upper half-plane, the trunk rising from the ground
  const W = 1400, H = 900, CX = W / 2, GY = H - 60, TRUNK = 90, R = 720, A0 = Math.PI * 0.06, A1 = Math.PI * 0.94;
  d3.tree().size([A1 - A0, 1]).separation((a, b) => (a.parent === b.parent ? 1 : 1.5) / Math.max(1, a.depth))(root);
  const maxDepth = Math.max(2, d3.max(root.descendants(), d => d.depth));
  const pos = (th, r) => r <= 0 ? [CX, GY] : [CX - r * Math.cos(th), GY - TRUNK - r * Math.sin(th)];
  root.each(d => { d.th = A0 + d.x; d.r = d.depth === 0 ? 0 : 60 + Math.pow((d.depth - 1) / (maxDepth - 1), 0.55) * (R - 60); [d.px, d.py] = pos(d.th, d.r); });
  function linkPath(p, c) {
    const rm = (p.r + c.r) / 2;
    const [x1, y1] = p.r === 0 ? [CX, GY - TRUNK * 0.95] : pos(p.th, rm);
    const [x2, y2] = pos(c.th, p.r === 0 ? c.r * 0.35 : rm);
    return `M${p.px},${p.py}C${x1},${y1} ${x2},${y2} ${c.px},${c.py}`;
  }
  const cls = c => { const n = c.data.node; if (!n) return "limb"; return n.partial ? "partial" : n.s === "frontier" ? "frontier" : "wood"; };
  const width = c => { const k = cls(c), s = Math.sqrt(c.w); return k === "wood" || k === "limb" ? 1.2 + 1.25 * s : k === "partial" ? 1.3 + 0.7 * s : 1 + 0.45 * s; };

  const svg = d3.select("#tree").attr("viewBox", `0 0 ${W} ${H}`).attr("preserveAspectRatio", "xMidYMid meet");
  const g = svg.append("g");
  const zoom = d3.zoom().scaleExtent([0.6, 6]).on("zoom", e => { g.attr("transform", e.transform); g.classed("zoomed", e.transform.k > 1.7); });
  svg.call(zoom);
  g.append("rect").attr("class", "t-ground").attr("x", -2000).attr("y", GY).attr("width", W + 4000).attr("height", 400);
  g.append("text").attr("class", "t-groundtxt").attr("x", CX).attr("y", GY + 24).text("Mathlib · BrownianMotion");

  const all = root.descendants(), byId = new Map(all.map(d => [d.id, d]));
  const links = all.filter(d => d.parent).sort((a, b) => b.w - a.w);
  const lk = g.append("g").selectAll("path").data(links).join("path")
    .attr("class", d => "t-lk " + cls(d)).attr("d", d => linkPath(d.parent, d)).attr("stroke-width", width);
  const secData = [];
  for (const d of all) { const n = d.data.node; if (!n) continue; for (const u of n.u) { if (u === d.parent?.id) continue; const p = byId.get(u); if (p) secData.push({s: p, t: d}); } }
  const sec = g.append("g").selectAll("path").data(secData).join("path").attr("class", "t-sec")
    .attr("d", e => `M${e.s.px},${e.s.py}Q${(e.s.px + e.t.px) / 2},${Math.min(e.s.py, e.t.py) - 40} ${e.t.px},${e.t.py}`);
  g.append("g").selectAll("text").data(all.filter(d => d.data.limb)).join("text").attr("class", "t-limb")
    .attr("x", d => d.px).attr("y", d => d.py - 6)
    .attr("text-anchor", d => d.th < Math.PI * 0.45 ? "end" : d.th > Math.PI * 0.55 ? "start" : "middle")
    .attr("dx", d => d.th < Math.PI * 0.45 ? -6 : d.th > Math.PI * 0.55 ? 6 : 0).text(d => d.data.limb);

  function rng(seed) { let s = 0; for (const ch of seed) s = (s * 31 + ch.charCodeAt(0)) | 0; return () => ((s = (s * 1103515245 + 12345) | 0) >>> 0) / 4294967296; }
  const BUD = {ready: "ready", "blocked-design": "design", "blocked-upstream": "up", research: "research", "in-progress": "prog"};
  const leaves = g.append("g").attr("class", "t-leaves"), buds = g.append("g").attr("class", "t-buds");
  for (const d of all) {
    const n = d.data.node; if (!n) continue; const rand = rng(n.l);
    const ox = -Math.cos(d.th) * 4, oy = -Math.sin(d.th) * 4;
    for (let k = 0; k < n.e; k++) {
      const a = d.th + (rand() - 0.5) * 1.6 + Math.PI, rr = 7 + Math.sqrt(rand()) * (8 + Math.sqrt(n.e) * 3.2);
      const x = d.px + Math.cos(a) * rr + ox, y = d.py + Math.sin(a) * rr * 0.9 + oy;
      leaves.append("ellipse").attr("class", "t-leaf").attr("cx", x).attr("cy", y).attr("rx", 2.1).attr("ry", 1.3).attr("transform", `rotate(${rand() * 180},${x},${y})`);
    }
    n.open.forEach((x, k) => {
      const a = d.th + Math.PI + (k - (n.open.length - 1) / 2) * 0.32;
      buds.append("circle").attr("class", "t-bud " + (BUD[x[4][0]] || "ready")).attr("r", 3)
        .attr("cx", d.px + Math.cos(a) * 11).attr("cy", d.py + Math.sin(a) * 11).append("title").text(`#${x[0]} ${x[3]}`);
    });
  }
  const nodes = g.append("g").selectAll("g").data(all.filter(d => d.data.node)).join("g")
    .attr("class", d => { const n = d.data.node; return "t-nd " + (n.partial ? "partial" : n.s); })
    .attr("transform", d => `translate(${d.px},${d.py})`).attr("tabindex", 0).attr("role", "button")
    .attr("aria-label", d => d.data.node.t);
  nodes.each(function (d) {
    const s = d3.select(this), n = d.data.node;
    if (n.s === "upstream") s.append("rect").attr("class", "m").attr("x", -5).attr("y", -5).attr("width", 10).attr("height", 10);
    else s.append("circle").attr("class", "m").attr("r", wood(n) ? 4.2 : 3.6);
    const left = d.th < Math.PI / 2;
    s.append("text").attr("class", wood(n) && d.w >= 10 ? "" : "t-zoomlbl").attr("x", left ? -8 : 8).attr("y", 3.5)
      .attr("text-anchor", left ? "end" : "start").text(n.t.length > 46 ? n.t.slice(0, 44) + "…" : n.t);
  });

  // ---- interaction
  const usesClosure = l => { const set = new Set([l]), st = [l]; while (st.length) { const n = N.get(st.pop()); if (!n) continue; for (const u of n.u) if (!set.has(u)) { set.add(u); st.push(u); } } return set; };
  function highlight(d) {
    if (!d) { g.classed("t-dim", false); nodes.classed("hi", false); lk.classed("hi", false); sec.classed("on", false); return; }
    const set = usesClosure(d.id);
    for (const n of DATA.nodes) if (n.u.includes(d.id)) set.add(n.l);
    g.classed("t-dim", true); nodes.classed("hi", x => set.has(x.id));
    lk.classed("hi", x => set.has(x.id) && (set.has(x.parent.id) || !x.parent.data.node));
    sec.classed("on", e => set.has(e.s.id) && set.has(e.t.id));
  }
  const tip = document.getElementById("tree-tip"), box = document.getElementById("tree-box");
  let selected = null;
  nodes.on("mouseenter", (ev, d) => { if (!selected) highlight(d); const r = box.getBoundingClientRect();
      tip.textContent = d.data.node.t; tip.style.left = (ev.clientX - r.left + 12) + "px"; tip.style.top = (ev.clientY - r.top + 12) + "px"; tip.style.opacity = 1; })
    .on("mouseleave", () => { tip.style.opacity = 0; if (!selected) highlight(null); })
    .on("click", (ev, d) => select(d.id))
    .on("keydown", (ev, d) => { if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); select(d.id); } });
  svg.on("click", ev => { if (ev.target.tagName === "svg" || ev.target.classList.contains("t-ground")) select(null); });

  const STATUS = {proved: "proved", upstream: "upstream", frontier: "frontier", partial: "core proved"};
  const panel = document.getElementById("tree-panel"), intro = panel.innerHTML;
  function show(l) {
    if (!l) { panel.innerHTML = intro; return; }
    const n = N.get(l), st = n.partial ? "partial" : n.s;
    const iss = n.i || [], open = iss.filter(x => x[1] === "o"), rec = iss.filter(x => x[1] !== "o");
    const li = x => `<li><a class="mono" href="${GH}${x[0]}">#${x[0]}</a> ${esc(x[3])}${x[2] ? ' <span class="ink2">(PR)</span>' : ""}${x[4][0] ? ` <span class="ink2">· ${esc(x[4][0])}</span>` : ""}</li>`;
    const chips = ls => ls.filter(u => N.has(u)).map(u => `<button type="button" class="t-chip" data-l="${esc(u)}">${esc(N.get(u).t)}</button>`).join("");
    const users = DATA.nodes.filter(m => m.u.includes(l)).map(m => m.l);
    panel.innerHTML = `<p><span class="t-pill ${st}">${STATUS[st]}</span> <span class="ink2">${esc(n.a)}</span></p>
      <h3>${esc(n.t)}</h3><p>${esc(n.x)}</p>
      ${n.d ? `<p class="mono t-decl">${n.h ? `<a href="${esc(n.h)}">${esc(n.d)}</a>` : esc(n.d)}</p>` : ""}
      ${n.partial ? `<p class="t-note">Proved in part: ${n.core.map(c => `<code>${esc(c)}</code>`).join(", ")}.</p>` : ""}
      ${n.ground ? `<p class="t-note">Builds on upstream material only: ${esc(n.ground)}.</p>` : ""}
      ${n.e ? `<p class="ink2">${n.e} corpus ${n.e === 1 ? "entry rests" : "entries rest"} here.</p>` : ""}
      ${n.u.length ? `<p class="ink2 t-sub">Builds on</p><div class="t-chips">${chips(n.u)}</div>` : ""}
      ${users.length ? `<p class="ink2 t-sub">Used by</p><div class="t-chips">${chips(users)}</div>` : ""}
      ${DATA.issues ? `<p class="ink2 t-sub">Open issues (${open.length})</p>${open.length ? `<ul class="t-issues">${open.map(li).join("")}</ul>` : ""}
      ${rec.length ? `<p class="ink2 t-sub">Delivered by</p><ul class="t-issues">${rec.map(li).join("")}</ul>` : ""}` : ""}`;
    panel.querySelectorAll("[data-l]").forEach(b => b.addEventListener("click", () => focus(b.dataset.l)));
  }
  function select(l) { selected = l; nodes.classed("sel", d => d.id === l); highlight(l ? byId.get(l) : null); show(l); }
  function focus(l) {
    const d = byId.get(l); if (!d) return;
    box.scrollIntoView({behavior: matchMedia("(prefers-reduced-motion: reduce)").matches ? "auto" : "smooth", block: "start"});
    svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity.translate(W / 2 - 2.2 * d.px, H / 2 - 2.2 * d.py).scale(2.2));
    select(l);
  }
  const on = (id, f) => { const x = document.getElementById(id); if (x) x.addEventListener("change", e => f(e.target.checked)); };
  on("t-buds", v => g.classed("t-nobuds", !v));
  on("t-leaves", v => g.classed("t-noleaves", !v));
  document.getElementById("t-reset").addEventListener("click", () => { svg.transition().duration(400).call(zoom.transform, d3.zoomIdentity); select(null); });
  document.querySelectorAll("[data-focus]").forEach(b => b.addEventListener("click", () => focus(b.dataset.focus)));
  if (location.hash.length > 1 && N.has(decodeURIComponent(location.hash.slice(1)))) focus(decodeURIComponent(location.hash.slice(1)));
})();
