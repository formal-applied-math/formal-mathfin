/* The program tree (tree.html): the blueprint drawn as a tree, grown from Mathlib and
 BrownianMotion. On a limb, height is MEASURED: a node sits at its hop, the distance in statements
 from the trunk (tools/verify/chain_reach.py), not at the order of the taxonomy; the roots and the
 trunk keep their depth of use. A node at infinite distance is an island, floating beside its limb
 under its cluster's name (red ring: nothing reaches it, nothing declares it); a tower of modules
 is one square node; a connector is a hollow dashed phantom between the nodes its statement
 mentions, sized by its gain. Every use is drawn as wood, and wood thickens with the corpus it
 carries; the use that sets a node's primary parent is drawn in bark, the others lighter. Corpus entries are leaves on the
 deepest node their proof rests on; off-map entries lie on the ground. Labels are sized in screen
 pixels and fill in with zoom. The gaps (connectors, islands), the frontier and the leaves are
 layers behind buttons, and a proof's secondary uses show only with its lineage. Data: the JSON block #tree-data, written by tools/verify/docs_site.py
 from program_tree.tree_data. Needs d3 and KaTeX (loaded by the page). */
(function () {
"use strict";
const el = document.getElementById("tree-data");
if (!el || !window.d3) return;
const D = JSON.parse(el.textContent);
const GH = D.repo + "/issues/";
const esc = s => String(s ?? "").replace(/[&<>"]/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));
const N = new Map(D.nodes.map(n => [n.l, n]));
const isUp = n => n.s === "upstream";
const isWood = n => n.s === "proved" || n.s === "partial";
const STATUS_RANK = ["in-progress","ready","research","blocked-design","blocked-upstream","needs-info"];
const STATUS_TXT = {"in-progress":"in progress", ready:"ready to pick up", research:"research", "blocked-design":"blocked on design", "blocked-upstream":"blocked upstream", "needs-info":"needs info"};
const STATUS_VAR = {"in-progress":"--tr-progress", ready:"--tr-ready", research:"--tr-research", "blocked-design":"--tr-blocked", "blocked-upstream":"--tr-blocked", "needs-info":"--tr-blocked"};
// cells, parts and families come from docs/taxonomy.toml, through program_tree.tree_data
const cellName = c => D.cellName[c] || c;
const FAM = new Map(D.families.map(f => [f.key, f]));
const famVar = n => n.f && FAM.get(n.f) ? `var(${FAM.get(n.f).hue})` : null;
// statement prose: TeX between dollars is typeset (KaTeX, MathML output: no stylesheet or fonts to fetch);
// outside it, `code` and *emphasis* are the blueprint's own markup
const tex = m => { try { return window.katex.renderToString(m, {throwOnError:false}); } catch (e) { return esc("$" + m + "$"); } };
const prose = t => String(t ?? "").split(/(\$[^$]*\$)/).map((seg, i) => i % 2 ? tex(seg.slice(1, -1))
  : esc(seg).replace(/`([^`]+)`/g, "<code>$1</code>").replace(/\*([^*\s][^*]*)\*/g, "<em>$1</em>")).join("");

for (const n of D.nodes){
  n.users = [];
  n.open = n.i.filter(x => x[1] === "o");
  const sts = n.open.map(x => x[4][0] || "ready");
  n.ist = STATUS_RANK.find(s => sts.includes(s)) || (n.open.length ? "ready" : null);   // its open issues
  n.st = n.s === "frontier" ? n.ist : null;
}
for (const n of D.nodes) for (const u of n.u) N.get(u)?.users.push(n.l);

// DAG depth, upstream treated as ground
const depthMemo = new Map();
function depth(l, seen = new Set()){
  if (depthMemo.has(l)) return depthMemo.get(l);
  const n = N.get(l); seen.add(l);
  const us = n.u.filter(u => N.has(u) && !isUp(N.get(u)) && !seen.has(u));
  const d = us.length ? 1 + Math.max(...us.map(u => depth(u, seen))) : 0;
  depthMemo.set(l, d); return d;
}
function hash(s){ let h = 2166136261; for (const c of s) h = Math.imul(h ^ c.charCodeAt(0), 16777619); return (h >>> 0) / 4294967296; }
function rng(seed){ let s = Math.floor(hash(seed) * 4294967295) | 0; return () => ((s = Math.imul(s ^ (s >>> 15), 2246822507) + 0x6D2B79F5 | 0) >>> 0) / 4294967296; }

// ---------- layout: the taxonomy places the nodes (docs/taxonomy.toml); the proofs draw the wood ----------
// The roots in the soil (one sector per root cell), positions and markets as the trunk, three limbs in
// sectors across the crown, each split into its branches; a joint sits in the gap between the two limbs
// it joins. A node's height counts only the uses inside its own part; an edge from another part is drawn
// as it is, so a pricing formula resting on a root rather than on the trunk shows as wood that bypasses it.
const W = 1600, CX = 800;
const pxPerUnit = () => (document.getElementById("tree").getBoundingClientRect().width || W) / W;
// the plate's fixed captions are drawn for a ~1300px stage; on a narrower one they grow, up to 1.7×
const TF = Math.min(1.7, Math.max(1, .8 / pxPerUnit()));
const cap = (sel, px) => sel.style("font-size", (px * TF).toFixed(1) + "px");
const PARTS = new Map(D.parts.map(p => [p.key, p]));
const kindOf = n => PARTS.get(n.p)?.kind || "limb";
const isRoot = n => kindOf(n) === "root", isTrunk = n => kindOf(n) === "trunk";
const isJoint = n => !!n.j;
const partTitle = p => PARTS.get(p)?.title || p;
const cellKey = n => n.p + (n.b ? "/" + n.b : "");
const cellTitle = k => cellName(k).split(" · ").pop();
const TRUNK = D.parts.find(p => p.kind === "trunk").key;
// layers the default view can leave out, each behind a button (data-layer in tree.html): the proofs,
// the map, towers and joints always show. "gaps": connectors and islands; "future": the mapped future
// work, the unproved blueprint nodes the open issues carry, joined in full to the proved node each
// rests on, and a ring on every proved node an open issue works on; "open": the open problems of the
// field (issues labelled open-problem); "leaves": the corpus, on the tree and on the ground.
const layerOf = n => n.ph ? "gaps" : n.op ? "open" : !isWood(n) && !isUp(n) && !n.tw ? "future" : null;
function layerOn(l){ return svg.classed("show-" + l); }   // svg is drawn before any caller runs
function shown(n){ return !layerOf(n) || layerOn(layerOf(n)); }
const layerCls = n => layerOf(n) ? " layer-" + layerOf(n) : "";
const live = D.nodes;
for (const n of live) n.depth = depth(n.l);
const mfUses = n => n.u.filter(u => N.has(u));
// a proved node outside the roots that rests on no node grows straight from the soil (Mathlib)
for (const n of live) n.sucker = !mfUses(n).length && !isRoot(n) && !n.isl;

// depth inside a node's own part
const pdMemo = new Map();
function pdepth(l, seen = new Set()){
  if (pdMemo.has(l)) return pdMemo.get(l);
  const n = N.get(l); seen.add(l);
  const us = n.u.filter(u => N.has(u) && !isUp(N.get(u)) && N.get(u).p === n.p && !seen.has(u));
  const d = us.length ? 1 + Math.max(...us.map(u => pdepth(u, seen))) : 0;
  pdMemo.set(l, d); return d;
}
for (const n of live) n.pd = pdepth(n.l);
// on a limb the level is the measured hop (a frontier node with no measured base sits at the first level)
const MAXLV = 6;
for (const n of live) if (kindOf(n) === "limb" && !isJoint(n))
  n.pd = n.isl ? 0 : Math.min(MAXLV, Math.max(0, (n.hp ?? 1) - 1));

// corpus flow: what each node carries, split evenly among the nodes it rests on
const own = n => isWood(n) ? 1 + n.e : .45;
const flow = new Map();
for (const n of live.slice().sort((x, y) => y.depth - x.depth)){
  let f = own(n);
  for (const m of n.users){ const mm = N.get(m); if (mm) f += (flow.get(m) || 0) / mfUses(mm).length; }
  flow.set(n.l, f);
}

// sectors: limbs across the crown, roots across the soil, each limb split into its branches
function sectors(keys, x0, x1, weight){
  const ws = keys.map(weight), tot = d3.sum(ws) || 1; let acc = x0; const out = new Map();
  keys.forEach((k, i) => { const w = (x1 - x0) * ws[i] / tot; out.set(k, {x0:acc, x1:acc + w, cx:acc + w / 2}); acc += w; });
  return out;
}
const inPart = p => live.filter(n => n.p === p && !isJoint(n) && !n.isl && !n.ph);
const islIn = k => D.islands.filter(c => c.p === k);
const islW = c => Math.max(7, 1.8 * Math.pow(c.nodes.length, .8));
const limbKeys = D.parts.filter(p => p.kind === "limb" && inPart(p.key).length).map(p => p.key);
// a root sector per root cell that holds a node: the branches of a root part, or the part itself
const rootKeys = D.parts.filter(p => p.kind === "root").flatMap(p => p.branches.length ? p.branches.map(b => p.key + "/" + b.key) : [p.key])
  .filter(k => live.some(n => isRoot(n) && cellKey(n) === k));
const inRoot = k => live.filter(n => isRoot(n) && cellKey(n) === k);
const GAP = 90;   // between neighbouring limbs: the fork, where the joints sit
const SEC = sectors(limbKeys, 40, W - 40, k => Math.max(6, Math.pow(inPart(k).length, .8) + d3.sum(islIn(k), islW)));
limbKeys.forEach((k, i) => { const s = SEC.get(k); if (i) s.x0 += GAP / 2; if (i < limbKeys.length - 1) s.x1 -= GAP / 2; });
const RSEC = sectors(rootKeys, 150, W - 150, k => Math.max(6, Math.pow(inRoot(k).length, .8)));
const BSEC = new Map();   // "limb/branch" -> sector
for (const k of limbKeys){
  const s = SEC.get(k), order = PARTS.get(k).branches.map(b => b.key);
  const present = [...order.filter(b => inPart(k).some(n => n.b === b)), ...(inPart(k).some(n => !order.includes(n.b)) ? [""] : [])];
  const isls = islIn(k).map(c => "~" + c.key);
  for (const [b, bs] of sectors([...present, ...isls], s.x0 + 6, s.x1 - 6, b => b[0] === "~" ? islW(islIn(k).find(c => "~" + c.key === b)) : Math.max(3, Math.pow(inPart(k).filter(n => (order.includes(n.b) ? n.b : "") === b).length, .8))))
    BSEC.set(k + "/" + b, bs);
}
// a joint sits in the fork between its two limbs
const jointKey = n => n.j.slice().sort().join("|");
const JSEC = n => { const [a, b] = n.j.map(k => SEC.get(k)).sort((p, q) => p.cx - q.cx);
  const x = a && b ? (a.x1 + b.x0) / 2 : CX; return {x0:x - GAP / 2 - 20, x1:x + GAP / 2 + 20, cx:x}; };
const ISL = new Map(D.islands.map(c => [c.key, c]));
const secOf = n => n.isl ? BSEC.get(ISL.get(n.isl).p + "/~" + n.isl) : isJoint(n) ? JSEC(n) : isTrunk(n) ? {x0:CX - 120, x1:CX + 120, cx:CX} : isRoot(n) ? RSEC.get(cellKey(n))
  : BSEC.get(n.p + "/" + (PARTS.get(n.p).branches.some(b => b.key === n.b) ? n.b : "")) || SEC.get(n.p);

// heights: the crown, the trunk, the ground, the roots, the bedrock. A level of a sector holding more
// knots than fit across it wraps into sub-rows, and the level grows by them, so a crowded branch
// grows taller instead of packing its results into one line.
const TOP = 30;
const LH = 92, TSTEP = 54, RSTEP = 46, SUBH = 46;
const phR = n => 9 + Math.min(12, Math.sqrt(n.ph.gain || 0) * 2.6);   // a connector: its gain
const rad = n => n.tw ? 16 : n.ph ? phR(n) + 4 : isWood(n) ? 10 + Math.sqrt(n.e) * 2.2 : n.op ? 14 : 8;
const sub = new Map(), subRows = new Map();   // node -> its sub-row; "kind|pd" -> most sub-rows
{ const groups = d3.group(live.filter(n => !isRoot(n) && !isUp(n) && !n.sucker && !n.isl && !n.ph),
    n => (isJoint(n) ? "joint/" + jointKey(n) : isTrunk(n) ? "trunk" : n.p + "/" + (n.b || "")) + "|" + n.pd);
  for (const [, g] of groups){
    const s = secOf(g[0]), need = d3.sum(g, n => 2 * rad(n) + 16);
    const k = Math.max(1, Math.ceil(need / Math.max(40, s.x1 - s.x0)));
    g.slice().sort((x, y) => hash(x.l) - hash(y.l)).forEach((n, i) => sub.set(n.l, i % k));
    const key = (isJoint(g[0]) ? "joint" : isTrunk(g[0]) ? "trunk" : "limb") + "|" + g[0].pd;
    subRows.set(key, Math.max(subRows.get(key) || 1, k));
  } }
// islands float: each cluster wraps into its own sub-rows, and they do not raise the limb
for (const [, g] of d3.group(live.filter(n => n.isl), n => n.isl)){
  const s = secOf(g[0]), k = Math.max(1, Math.ceil(d3.sum(g, n => 2 * rad(n) + 16) / Math.max(40, s.x1 - s.x0)));
  g.slice().sort((x, y) => hash(x.l) - hash(y.l)).forEach((n, i) => sub.set(n.l, i % k));
}
const maxIn = kind => d3.max(live.filter(n => kindOf(n) === kind && !isJoint(n) && !n.isl && !n.ph), n => n.pd) || 0;
// offset of each level above the first: the levels below it, each with its sub-rows
const offsets = (kind, step) => { const o = [0];
  for (let d = 1; d <= maxIn(kind); d++) o.push(o[d - 1] + step + ((subRows.get(kind + "|" + (d - 1)) || 1) - 1) * SUBH);
  return o; };
const LOFF = offsets("limb", LH), TOFF = offsets("trunk", TSTEP);
const crown = LOFF[LOFF.length - 1] + ((subRows.get("limb|" + maxIn("limb")) || 1) - 1) * SUBH;
const bole = TOFF[TOFF.length - 1] + ((subRows.get("trunk|" + maxIn("trunk")) || 1) - 1) * SUBH;
const LB = TOP + 40 + crown;                      // a limb's first level
const TT = LB + 70;                               // the trunk's top, where the limbs fork
const GY = TT + 60 + bole;                        // the ground
const ROW0 = GY + 10 + 14 * TF, ROWH = 17 * TF;   // pile labels just under the ground
const PROWS = 4;
const RT = ROW0 + PROWS * ROWH + 14;                  // the root band
const rootMax = new Map(rootKeys.map(k => [k, d3.max(inRoot(k), n => n.pd) || 0]));
// root captions sit under their root; one that would run into its left neighbour drops a line
const rootCap = new Map();
{ const placed = [];
  for (const k of rootKeys){
    const s = RSEC.get(k), w = cellTitle(k).length * 10.5 * TF / 2 + 6;
    let y = RT + 14 + rootMax.get(k) * RSTEP + 46 * TF;
    while (placed.some(q => Math.abs(q.x - s.cx) < q.w + w && Math.abs(q.y - y) < 44 * TF)) y += 40 * TF;
    placed.push({x:s.cx, y, w}); rootCap.set(k, y);
  } }
const BED = Math.max(...rootCap.values()) + 30 * TF;
const H = Math.round(BED + 64 * TF);
const yTarget = n => isUp(n) ? BED + 24 : isRoot(n) ? RT + 14 + (rootMax.get(cellKey(n)) - n.pd) * RSTEP
  : isJoint(n) ? LB + 24 - (sub.get(n.l) || 0) * SUBH
  : isTrunk(n) ? GY - 40 - TOFF[n.pd] - (sub.get(n.l) || 0) * SUBH
  : n.isl ? LB - Math.max(LH * 1.4, crown * .5) - (sub.get(n.l) || 0) * SUBH
  : n.sucker ? LB + 60 + hash(n.l) * 90
  : LB - LOFF[n.pd] - (sub.get(n.l) || 0) * SUBH;
const sim = live.filter(n => !n.ph).map(n => { const s = secOf(n); return {id:n.l, n, s, x:s.cx + (hash(n.l + "x") - .5) * (s.x1 - s.x0) * .8, y:yTarget(n)}; });
d3.forceSimulation(sim)
  .force("x", d3.forceX(s => s.s.cx).strength(.06))
  .force("y", d3.forceY(s => yTarget(s.n)).strength(.9))
  .force("collide", d3.forceCollide(s => rad(s.n)).strength(.9).iterations(3))
  .on("tick", () => { for (const s of sim) s.x = Math.max(s.s.x0 + 8, Math.min(s.s.x1 - 8, s.x)); })
  .stop().tick(360);
for (const s of sim) s.x = Math.max(s.s.x0 + 8, Math.min(s.s.x1 - 8, s.x));
// phantoms (connectors): between the nodes the statement mentions, at the height the hop would give it if proved
{ const at = new Map(sim.map(s => [s.id, s]));
  const ph = live.filter(n => n.ph).map(n => {
    // between the far end (an island, else the highest node it mentions) and the node it mentions
    // nearest the trunk, at the height of the far end
    const ends = n.u.map(u => at.get(u)).filter(Boolean);
    const far = ends.filter(e => !isTrunk(e.n)).sort((a, b) => (!!b.n.isl - !!a.n.isl) || a.y - b.y)[0] || ends[0];
    const near = ends.filter(e => e !== far).sort((a, b) => (isTrunk(a.n) - isTrunk(b.n)) || b.y - a.y)[0];
    n.phEnds = [far, near].filter(Boolean).map(e => e.id);
    const ex = !far ? CX : near ? (far.x + near.x) / 2 : far.x + 40, ey = far ? far.y - 30 : LB;
    return {id:n.l, n, x:ex, y:ey, tx:ex};
  });
  const fixed = sim.map(s => ({fx:s.x, fy:s.y, r:rad(s.n) * .5}));
  const all = [...fixed, ...ph];
  d3.forceSimulation(all)
    .force("x", d3.forceX(s => s.tx ?? s.fx).strength(s => s.n ? .08 : 0))
    .force("y", d3.forceY(s => s.n ? s.y : s.fy).strength(s => s.n ? .4 : 1))
    .force("collide", d3.forceCollide(s => s.n ? rad(s.n) : s.r).strength(.8).iterations(3))
    .stop().tick(240);
  for (const q of ph){ q.x = Math.max(24, Math.min(W - 24, q.x)); sim.push({id:q.id, n:q.n, x:q.x, y:q.y}); }
}
// levels for the growth animation: roots, then the trunk, then the limbs
const lvlOf = n => isRoot(n) ? n.pd : isTrunk(n) ? 8 + n.pd : 14 + n.pd;
const byId = new Map();
for (const s of sim){
  const n = s.n;
  byId.set(n.l, {id:n.l, data:{node:n}, px:s.x, py:s.y, up:isUp(n), depth:lvlOf(n), value:flow.get(n.l),
    seed:n.s === "frontier" && !mfUses(n).length});
}
const upNodes = [];

// the primary parent: the use nearest on the map (same branch, same limb, the trunk, a root), then the deepest
const near = (n, m) => m.p === n.p ? (m.b === n.b ? 4 : 3) : isTrunk(m) ? 2 : kindOf(m) === "limb" ? 1 : 0;
for (const n of live){
  const us = mfUses(n);
  n.prim = us.length ? us.reduce((a, b) => { const A = N.get(a), B = N.get(b);
    return (near(n, B) - near(n, A) || B.depth - A.depth || flow.get(b) - flow.get(a)) > 0 ? b : a; }) : null;
}
// edges: every use, drawn from the node it rests on up to the node that uses it
const edges = [];
for (const n of live){
  const t = byId.get(n.l), us = mfUses(n);
  for (const u of us) edges.push({s:byId.get(u), t, f:flow.get(n.l) / us.length, prim:n.ph ? !!n.phEnds?.includes(u) : u === n.prim});
  if (!us.length && !isRoot(n) && !n.isl) edges.push({s:null, base:[(isTrunk(n) ? CX : t.px) + (hash(n.l + "stem") - .5) * 20, GY + 6], t, f:flow.get(n.l), prim:true});
}
const BW = f => Math.min(22, .9 + 1.2 * Math.sqrt(f));
function dirOf(d){
  const n = d.data?.node; if (!n) return [0, -1];
  const ps = mfUses(n).map(u => byId.get(u)).filter(Boolean);
  const [mx, my] = ps.length ? [d3.mean(ps, p => p.px), d3.mean(ps, p => p.py)] : [d.px, d.py + 60];
  let v = [d.px - mx, d.py - my]; const l = Math.hypot(...v) || 1; v = [v[0] / l * .7, Math.min(-.35, v[1] / l)];
  const m = Math.hypot(...v); return [v[0] / m, v[1] / m];
}

// ---------- drawing ----------
const svg = d3.select("#tree").attr("viewBox", `0 0 ${W} ${H}`).style("aspect-ratio", `${W} / ${H}`);
const view = svg.append("g");

// soil: topsoil holds the roots, the bedrock is Mathlib and BrownianMotion
const ground = view.append("g");
const wave = (y, amp, ph) => d3.range(0, W + 41, 40).map(x => [x, y + Math.sin(x / 190 + ph) * amp]);
const area = (top, bot) => d3.area().x(p => p[0]).y0(p => p[1]).y1(bot).curve(d3.curveBasis)(top);
ground.append("path").attr("class", "soil-1").attr("d", area(wave(GY, 4, 0), H));
ground.append("path").attr("class", "soil-2").attr("d", area(wave(BED, 5, 1.7), H));
ground.append("path").attr("class", "ground-line").attr("d", d3.line().curve(d3.curveBasis)(wave(GY, 4, 0)));
cap(ground.append("text").attr("class", "stratum").attr("x", 30).attr("y", BED + 30 * TF).text("Mathlib · BrownianMotion"), 15);
cap(ground.append("text").attr("class", "stratum-sub").attr("x", 30).attr("y", BED + 50 * TF).text("measure, probability, analysis; Brownian motion upstream"), 16);
{ const r = rng("stones"); for (let k = 0; k < 60; k++){
  const x = r() * W, y = BED + 12 + r() * (H - BED - 20);
  if (x < 40 + 460 * TF && y < BED + 58 * TF) continue;
  ground.append("ellipse").attr("class", "stone").attr("cx", x).attr("cy", y).attr("rx", 2 + r() * 5).attr("ry", 1.2 + r() * 2.2); } }

function taper(P, c1, c2, C, w0, w1, steps = 18){
  const L = [], Rr = [];
  for (let i = 0; i <= steps; i++){
    const t = i / steps, u = 1 - t;
    const x = u*u*u*P[0] + 3*u*u*t*c1[0] + 3*u*t*t*c2[0] + t*t*t*C[0];
    const y = u*u*u*P[1] + 3*u*u*t*c1[1] + 3*u*t*t*c2[1] + t*t*t*C[1];
    const dx = 3*u*u*(c1[0]-P[0]) + 6*u*t*(c2[0]-c1[0]) + 3*t*t*(C[0]-c2[0]);
    const dy = 3*u*u*(c1[1]-P[1]) + 6*u*t*(c2[1]-c1[1]) + 3*t*t*(C[1]-c2[1]);
    const len = Math.hypot(dx, dy) || 1, h = (w0 + (w1 - w0) * t) / 2;
    L.push([x - dy / len * h, y + dx / len * h]); Rr.push([x + dy / len * h, y - dx / len * h]);
  }
  return "M" + L.map(p => p.map(v => v.toFixed(1)).join(",")).join("L") + "L" + Rr.reverse().map(p => p.map(v => v.toFixed(1)).join(",")).join("L") + "Z";
}

// the map, in pale wood: the trunk, a limb to each sector, a twig to each branch, a root to each root
const ghost = view.append("g").attr("class", "map-ghost dimmable");
const gw = k => 10 + 3.2 * Math.sqrt((PARTS.get(k) ? inPart(k) : inRoot(k)).length);
ghost.append("path").attr("class", "ghost").attr("d", taper([CX, GY + 8], [CX, GY - 60], [CX, TT + 40], [CX, TT], gw(TRUNK) * 1.8, gw(TRUNK) * 1.3));
// the pale wood of a limb ends at its highest measured node: no rays run on past the data
const topOf = (k, b) => d3.min(live.filter(n => n.p === k && !n.isl && !n.ph && !isJoint(n) && (b === undefined || (n.b || "") === b)), n => byId.get(n.l).py);
for (const k of limbKeys){
  const s = SEC.get(k), w = gw(k), ytop = Math.max(TOP + 20, topOf(k) ?? LB);
  const mid = LB - .5 * (LB - ytop);
  ghost.append("path").attr("class", "ghost").attr("d", taper([CX, TT + 6], [CX + (s.cx - CX) * .15, TT - 60], [s.cx, LB - 40], [s.cx, mid], w, w * .55));
  for (const [key, bs] of BSEC) if (key.startsWith(k + "/") && key[k.length + 1] !== "~"){
    const yb = Math.max(TOP + 20, topOf(k, key.slice(k.length + 1)) ?? mid) - 6;
    ghost.append("path").attr("class", "ghost").attr("d", taper([s.cx, mid + 4], [s.cx, mid - 20], [bs.cx, yb + 30], [bs.cx, yb], w * .4, 2.5));
  }
}
for (const k of rootKeys){
  const s = RSEC.get(k), w = gw(k), y1 = RT + 14 + rootMax.get(k) * RSTEP;
  ghost.append("path").attr("class", "ghost").attr("d", taper([CX, GY - 2], [CX, GY + 40], [s.cx, RT - 20], [s.cx, y1], w, 3));
}
const trunkLbl = cap(view.append("text").attr("class", "trunk-lbl").attr("x", CX).attr("y", ROW0).attr("text-anchor", "middle").text(partTitle(TRUNK)), 12);

// the proofs, in dark wood (and in blueprint ink where the node is still frontier)
const roots = view.append("g");          // kept for the growth animation
const linkG = view.append("g"), shootG = view.append("g");
function edgeGeom(e){
  const P = e.s ? [e.s.px, e.s.py] : e.base, C = [e.t.px, e.t.py], dy = Math.max(30, P[1] - C[1]);
  return {P, c1:[P[0], P[1] - dy * .55], c2:[C[0], C[1] + dy * .42], C};
}
const woodEdges = edges.filter(e => isWood(e.t.data.node) || e.t.up);
const shootEdges = edges.filter(e => !isWood(e.t.data.node) && !e.t.up);
const branchSel = linkG.selectAll("path").data(woodEdges.slice().sort((a, b) => a.prim - b.prim || b.f - a.f)).join("path")
  .attr("class", e => "branch dimmable" + (e.prim ? "" : " sec"))
  .attr("d", e => { const g = edgeGeom(e), w = BW(e.f); return taper(g.P, g.c1, g.c2, g.C, w * 1.15, Math.max(.8, w * .62)); });
// a connector's edges are dashed and straight-ish, heavier with its gain; a plain shoot rises from its base
// a plain frontier edge is a faint stub toward what it rests on (the full curve shows on hover or selection)
const STUB = 46;
// with its layer shown, a bud's primary shoot is drawn in full, down to the node it rests on
const fullShoot = e => e.prim && !e.t.data.node.ph && layerOn(layerOf(e.t.data.node));
function shootD(e, full){
  const n = e.t.data.node, C = [e.t.px, e.t.py];
  if (n.ph){ const P = [e.s.px, e.s.py]; return `M${P}Q${(P[0] + C[0]) / 2},${Math.min(P[1], C[1]) - 18} ${C}`; }
  const g = edgeGeom(e), len = Math.hypot(g.P[0] - C[0], g.P[1] - C[1]);
  if (full || len <= 150) return `M${g.P}C${g.c1} ${g.c2} ${g.C}`;
  const k = STUB / len; return `M${C[0] + (g.P[0] - C[0]) * k},${C[1] + (g.P[1] - C[1]) * k}L${C}`;
}
const shootSel = shootG.selectAll("path").data(shootEdges).join("path")
  .attr("class", e => (e.t.data.node.ph ? "shoot ph dimmable" : "shoot dimmable") + (e.prim ? "" : " sec") + layerCls(e.t.data.node))
  .attr("d", e => shootD(e, fullShoot(e)))
  .style("stroke-width", e => e.t.data.node.ph ? (1.2 + Math.sqrt(e.t.data.node.ph.gain || 0) * .45).toFixed(2) : null);

// islands: a dashed outline round each floating cluster, named; red when nothing reaches it
const islG = view.append("g").attr("class", "dimmable layer-gaps");
const islSel = islG.selectAll("g").data(D.islands.filter(c => c.nodes.some(l => byId.has(l)))).join("g").attr("class", c => "isl" + (c.ring ? " ring" : ""));
islSel.each(function(c){
  const g = d3.select(this), pts = c.nodes.map(l => byId.get(l)).filter(Boolean);
  const x0 = d3.min(pts, p => p.px) - 22, x1 = d3.max(pts, p => p.px) + 22, y0 = d3.min(pts, p => p.py) - 26, y1 = d3.max(pts, p => p.py) + 22;
  c.box = {cx:(x0 + x1) / 2, cy:(y0 + y1) / 2, rx:Math.max(34, (x1 - x0) / 2), ry:Math.max(30, (y1 - y0) / 2), top:y0, bot:y1};
  g.append("ellipse").attr("class", "isl-ring").attr("cx", c.box.cx).attr("cy", c.box.cy).attr("rx", c.box.rx).attr("ry", c.box.ry);
  const t = cap(g.append("text").attr("class", "isl-lbl").attr("x", c.box.cx).attr("y", islIn(c.p).indexOf(c) % 2 ? y1 + 15 * TF : y0 - 6).attr("text-anchor", "middle"), 12.5);
  const words = c.title.replace(/^[^·]*·\s*/, "");
  t.text(words.length > 22 ? words.slice(0, 21).trimEnd() + "…" : words);
  c.lbl = t;
  g.append("title").text(c.declared ? `${c.title}: standalone. ${c.reason}${c.socket ? " Read in a market by " + c.socket + "." : ""}` : c.ring ? `${c.title}: no statement joins it to the trunk, no connector reaches it, and nothing declares why.` : `${c.title}: no statement joins it to the trunk yet; a connector would.`);
  g.append("rect").attr("class", "hit").attr("x", x0).attr("y", y0 - 16).attr("width", x1 - x0).attr("height", 18);
});

// island labels: inside the canvas and apart, above or below the ring in turn, then pushed along x
for (const row of [0, 1]){
  const items = D.islands.filter(c => c.lbl && islIn(c.p).indexOf(c) % 2 === row).map(c => ({c, x:c.box.cx, w:c.lbl.node().getComputedTextLength() + 26}));
  relax(items);
  for (const L of items) L.c.lbl.attr("x", L.x);
}

// captions: root names in the soil
const limbLbl = view.append("g").attr("class", "dimmable");
function relax(items){
  items.sort((p, q) => p.x - q.x);
  for (let it = 0; it < 80; it++){
    let moved = false;
    for (let i = 1; i < items.length; i++){ const p = items[i - 1], q = items[i], need = (p.w + q.w) / 2 - (q.x - p.x); if (need > 0){ p.x -= need / 2; q.x += need / 2; moved = true; } }
    for (const L of items) L.x = Math.max(L.w / 2 + 8, Math.min(W - L.w / 2 - 8, L.x));
    if (!moved) break;
  }
  return items;
}
for (const k of rootKeys){
  const s = RSEC.get(k), y = rootCap.get(k);
  cap(limbLbl.append("text").attr("class", "root-lbl").attr("x", s.cx).attr("y", y).attr("text-anchor", "middle").text(cellTitle(k)), 13.5)
    .append("title").text(D.cellBlurb[k] || cellName(k));
}

// leaves: one per corpus entry resting on the node
const leafG = view.append("g").attr("class", "layer-leaves");
const LEAF = "M0,0 C2.2,-2.6 5.6,-2.6 8,0 C5.6,2.6 2.2,2.6 0,0Z";
const leafData = [];
for (const d of byId.values()){
  const n = d.data.node; if (!n.e) continue;
  const r = rng(n.l), [ux, uy] = dirOf(d), base = Math.atan2(uy, ux);
  for (let k = 0; k < n.e; k++){
    const a = base + (r() - .5) * 3.3, rr = 5 + Math.sqrt(r()) * (9 + Math.sqrt(n.e) * 4.4);
    leafData.push({d, x:d.px + Math.cos(a) * rr, y:d.py + Math.sin(a) * rr, rot:a * 180 / Math.PI + (r() - .5) * 70, s:1.15 + r() * .7, c:1 + Math.floor(r() * 3), k});
  }
}
const leafSel = leafG.selectAll("path").data(leafData).join("path")
  .attr("class", f => `leaf l${f.c} dimmable`).attr("d", LEAF)
  .attr("transform", f => `translate(${f.x.toFixed(1)},${f.y.toFixed(1)}) rotate(${f.rot.toFixed(0)}) scale(${f.s.toFixed(2)})`);

// fallen leaves: proved entries off the map, under the part of the map their directory belongs to
const litterG = view.append("g").attr("class", "layer-leaves");
// piles: a root cell keeps its own, a limb's cells share the limb's pile
const pileKey = c => RSEC.has(c) ? c : c.split("/")[0];
const pileName = a => (PARTS.has(a) ? partTitle(a) : cellTitle(a)).split(" and ")[0].slice(0, 18);
const byPile = new Map();
for (const [c, l] of Object.entries(D.off)) for (const e of l){
  const a = pileKey(c); if (!byPile.has(a)) byPile.set(a, []); byPile.get(a).push([...e, cellTitle(c)]); }
const piles = [...byPile].map(([a, list]) => ({a, list}));
const pileHome = a => RSEC.get(a) || SEC.get(a) || {cx:CX};
const pileX = new Map(); { const used = [{x:CX, half:trunkLbl.node().getComputedTextLength() / 2 + 4}];
  for (const p of piles.sort((x, y) => y.list.length - x.list.length)){
    let x = pileHome(p.a).cx; const half = 14 + Math.sqrt(p.list.length) * 6.5;
    const free = c => c >= 30 + half && c <= W - 30 - half && !used.some(u => Math.abs(u.x - c) < u.half + half + 12);
    for (let off = 0; off < W; off += 6){ if (free(x + off)){ x += off; break; } if (free(x - off)){ x -= off; break; } }
    used.push({x, half}); pileX.set(p.a, {x, half}); }
}
const pileSel = litterG.selectAll("g").data(piles).join("g").attr("class", "pile dimmable");
pileSel.each(function(p){
  const g = d3.select(this), {x, half} = pileX.get(p.a), r = rng("pile" + p.a);  // half: leaf spread
  for (let k = 0; k < p.list.length; k++){
    const fx = x + (r() + r() - 1) * half, fy = GY - 4 + (r() - .3) * 9 - Math.max(0, 1 - Math.abs(fx - x) / half) * 5;
    g.append("path").attr("class", "fallen").attr("d", LEAF).attr("transform", `translate(${fx.toFixed(1)},${fy.toFixed(1)}) rotate(${(r() * 360).toFixed(0)}) scale(${(.75 + r() * .4).toFixed(2)})`);
  }
  cap(g.append("text").attr("class", "pile-lbl").attr("x", x).attr("y", ROW0).text(`${p.list.length} ${pileName(p.a)}`), 13.5);
  g.append("title").text(`${p.list.length} ${pileName(p.a)} entries off the map`);
  g.append("rect").attr("class", "hit").attr("x", x - half - 8).attr("y", GY - 18).attr("width", 2 * half + 16).attr("height", 24 + 20 * TF);
});
// pile labels, measured: the first row with room, else the next one down
{ const rows = [[{x:CX, lw:trunkLbl.node().getComputedTextLength() / 2 + 8 * TF}], ...Array.from({length:PROWS - 1}, () => [])], pad = 10 * TF;
  const lbls = []; pileSel.each(function(p){ const t = d3.select(this).select(".pile-lbl"); lbls.push({t, x:pileX.get(p.a).x, lw:t.node().getComputedTextLength() / 2 + pad}); });
  for (const L of lbls){ L.x = Math.max(L.lw + 6, Math.min(W - L.lw - 6, L.x)); L.t.attr("x", L.x); }
  for (const L of lbls.sort((a, b) => a.x - b.x)){
    const r = rows.findIndex(row => !row.some(u => Math.abs(u.x - L.x) < u.lw + L.lw));
    if (r < 0){ L.t.attr("display", "none"); continue; }   // no free row: the pile keeps its tooltip
    rows[r].push(L); L.t.attr("y", ROW0 + r * ROWH);
  } }
// upstream-only entries as seeds in the bedrock
const upOnly = Object.values(D.areas).reduce((s, c) => s + (c["upstream-only"] || 0), 0);
const seedbed = view.append("g").attr("class", "seedbed dimmable layer-leaves");
{ const r = rng("seedbed"), x0 = W - 330;
  for (let k = 0; k < upOnly; k++) seedbed.append("ellipse").attr("class", "seedmark").attr("cx", x0 + r() * 270).attr("cy", BED + 16 + r() * (H - BED - 44)).attr("rx", 2.4).attr("ry", 1.5);
  cap(seedbed.append("text").attr("class", "stratum-sub").attr("x", x0 + 270).attr("y", H - 12).attr("text-anchor", "end").text(`${upOnly} entries cite Mathlib alone`), 16);
  seedbed.append("rect").attr("class", "hit").attr("x", x0 - 6).attr("y", BED + 6).attr("width", 282).attr("height", H - BED - 6); }

// nodes
const nodeG = view.append("g");
const nodeData = [...byId.values()].filter(d => d.data && d.data.node);
const STAR = (r) => d3.range(12).map(i => { const a = -Math.PI / 2 + i * Math.PI / 6, rr = i % 2 ? r * .45 : r; return [Math.cos(a) * rr, Math.sin(a) * rr]; });
const isOP = n => !!n.op;
const nodeSel = nodeG.selectAll("g").data(nodeData).join("g").attr("class", d => "nd dimmable" + layerCls(d.data.node)).attr("transform", d => `translate(${d.px},${d.py})`);
nodeSel.each(function(d){
  const g = d3.select(this), n = d.data.node;
  if (d.up){ g.append("ellipse").attr("rx", 11).attr("ry", 6.5).attr("class", "knot"); cap(g.append("text").attr("class", "stratum-sub").attr("x", 18).attr("y", 5).text(n.t), 16); }
  else if (n.tw){
    const r = 12, k = g.append("rect").attr("class", "knot tower").attr("x", -r).attr("y", -r).attr("width", 2 * r).attr("height", 2 * r).attr("rx", 3);
    if (famVar(n)) k.style("fill", famVar(n));
    g.append("text").attr("class", "tower-n").attr("y", 3.5).attr("text-anchor", "middle").text(n.tw); }
  else if (isWood(n)){
    const k = g.append("circle").attr("r", 2.6 + Math.min(6.4, Math.sqrt(n.e) * 1.05)).attr("class", "knot" + (n.s === "partial" ? " partial" : ""));
    if (famVar(n)) k.style(n.s === "partial" ? "stroke" : "fill", famVar(n));
    if (n.open.length) g.append("circle").attr("r", 2.6 + Math.min(6.4, Math.sqrt(n.e) * 1.05) + 3.2)
      .attr("class", "iss-ring layer-future").style("stroke", `var(${STATUS_VAR[n.ist]})`); }
  else if (n.ph){
    const fv = famVar(n), r = phR(n);
    g.append("circle").attr("r", r).attr("class", "phantom").style("stroke", fv);
    g.append("text").attr("class", "ph-n").attr("y", 4).attr("text-anchor", "middle").text("+" + (n.ph.gain || 0)); }
  else if (isOP(n)){ g.append("circle").attr("r", 13).attr("class", "halo"); g.append("path").attr("class", "star").attr("d", "M" + STAR(7.5).join("L") + "Z"); }
  else {
    const fv = famVar(n);
    g.append("circle").attr("r", 4.6).attr("class", "bud").style("stroke", fv);
    if (n.core && n.core.length) g.append("path").attr("class", "bud-core").attr("d", "M0,-4.6 A4.6,4.6 0 0 0 0,4.6 Z").style("fill", fv);
    g.append("circle").attr("r", 1.7).attr("cx", n.core && n.core.length ? 1.9 : 0).attr("class", "bud-dot st-" + (n.st || "none"));
  }
  g.append("circle").attr("r", d.up ? 14 : 9).attr("class", "hit");
});

nodeSel.filter(d => d.data.node.ph).raise();   // connectors sit above everything else

// labels: sized in screen pixels, tried at four spots around the node, never over a knot or another label
const lblG = view.append("g");
function shortTitle(t, max){ let s = t.replace(/\s*\(.*?\)\s*/g, " ").replace(/\s+—.*$/, "").replace(/:.*$/, "").trim(); return s.length > max ? s.slice(0, max - 1).trimEnd() + "…" : s; }
const lblData = nodeData.filter(d => !d.up).map(d => {
  const n = d.data.node, [ux, uy] = d.seed ? [0, -1] : dirOf(d);
  const side = Math.abs(ux) < .28 ? 0 : (ux < 0 ? -1 : 1);
  const pr = isOP(n) ? 1e6 : n.ph ? 5e5 + n.ph.gain : isWood(n) ? d.value * 10 + n.e : (n.st === "ready" ? 3 : 1);
  const tail = n.tw ? ` · ${n.tw} modules` : "";
  return {d, n, side, pr, full: shortTitle(n.t, 46) + tail, short: shortTitle(n.t, 34) + tail};
});
const lblSel = lblG.selectAll("text").data(lblData).join("text")
  .attr("class", L => "lbl dimmable" + (isOP(L.n) ? " op" : L.n.ph ? " ph" : !isWood(L.n) ? " fr" : "") + layerCls(L.n));
const glyphR = d => { const n = d.data.node; return n.tw ? 12 : n.ph ? phR(n) : isWood(n) ? 2.6 + Math.min(6.4, Math.sqrt(n.e) * 1.05) : isOP(n) ? 8 : 4.6; };
let curK = 1, litSet = null;
function placeLabels(k = curK, set = litSet){
  curK = k;
  const s = pxPerUnit() * k, fs = (k < 1.4 ? 13 : 12.5) / s, h = fs * 1.2, pad = 3 / s;
  const boxes = [];
  if (!set) for (const el of document.querySelectorAll("#tree .root-lbl, #tree .root-sub, #tree .trunk-lbl" + (layerOn("gaps") ? ", #tree .isl-lbl" : ""))){
    const b = el.getBBox(); boxes.push([b.x, b.y, b.x + b.width, b.y + b.height, "cap"]); }
  for (const d of nodeData) if (!d.up && (set ? set.has(d.id) : shown(d.data.node))){ const r = glyphR(d) + 1.5; boxes.push([d.px - r, d.py - r, d.px + r, d.py + r, d.id]); }
  const hit = (b, self) => boxes.some(c => c[4] !== self && !(b[2] < c[0] || b[0] > c[2] || b[3] < c[1] || b[1] > c[3]));
  const eligible = L => set ? set.has(L.d.id) : !shown(L.n) ? false
    : k < 1.4 ? isWood(L.n) || isOP(L.n) || !!L.n.ph
    : k < 2.4 ? isWood(L.n) || isOP(L.n) || L.n.st === "ready" : true;
  const budget = set ? 1e9 : k < 1.4 ? 30 : k < 2.4 ? 80 : 1e9;
  const order = lblData.filter(eligible).sort((a, b) => (b.d.id === selected) - (a.d.id === selected) || b.pr - a.pr);
  const show = new Map();
  for (const L of order){
    if (show.size >= budget) break;
    const text = k < 1.4 && !set ? L.short : L.full, w = text.length * fs * .56;
    const o = glyphR(L.d) + 4 / s;
    const spots = [[1, 0], [-1, 0], [0, -1], [0, 1]];
    if (L.side < 0) spots.unshift(spots.splice(1, 1)[0]); else if (L.side === 0 && L.d.seed) spots.unshift(spots.splice(2, 1)[0]);
    for (const [sx, sy] of spots){
      const x = L.d.px + sx * o, y = L.d.py + sy * (o + h * .5);
      const x0 = sx > 0 ? x : sx < 0 ? x - w : x - w / 2, y0 = y - h / 2;
      const b = [x0 - pad, y0 - pad, x0 + w + pad, y0 + h + pad, L.d.id];
      if (hit(b, L.d.id) || b[0] < 4 || b[2] > W - 4) continue;
      boxes.push(b); show.set(L, {x, y: y + fs * .36, anchor: sx > 0 ? "start" : sx < 0 ? "end" : "middle", text}); break;
    }
  }
  lblSel.classed("show", L => show.has(L)).classed("on", L => show.has(L)).classed("sel", L => L.d.id === selected)
    .attr("font-size", fs).attr("stroke-width", 4 / s)
    .each(function(L){ const p = show.get(L); if (!p) return; d3.select(this).attr("x", p.x).attr("y", p.y).attr("text-anchor", p.anchor).text(p.text); });
}

for (const el of document.querySelectorAll("#tree .root-lbl, #tree .root-sub, #tree .trunk-lbl")) view.node().insertBefore(el, nodeG.node());
const selRing = view.append("circle").attr("class", "sel-ring").attr("r", 12).attr("visibility", "hidden");

// ---------- zoom ----------
const zoom = d3.zoom().scaleExtent([1, 9]).translateExtent([[0, 0], [W, H]])
  .on("zoom", e => { view.attr("transform", e.transform); })
  .on("end", e => placeLabels(e.transform.k));
new ResizeObserver(() => placeLabels()).observe(document.getElementById("tree"));
svg.call(zoom).on("dblclick.zoom", null);
document.getElementById("t-reset").onclick = () => svg.transition().duration(600).call(zoom.transform, d3.zoomIdentity);
document.getElementById("t-zin").onclick = () => svg.transition().duration(350).call(zoom.scaleBy, 1.6);
document.getElementById("t-zout").onclick = () => svg.transition().duration(350).call(zoom.scaleBy, 1 / 1.6);
function focusOn(d, k = 2.6){
  svg.transition().duration(650).call(zoom.transform, d3.zoomIdentity.translate(W / 2 - k * d.px, H * .45 - k * d.py).scale(k));
}

// ---------- lineage highlight ----------
function lineage(l){
  const down = new Set([l]), up = new Set([l]);
  const st = [l]; while (st.length){ const x = st.pop(); for (const u of N.get(x)?.u || []) if (!down.has(u)){ down.add(u); st.push(u); } }
  const st2 = [l]; while (st2.length){ const x = st2.pop(); for (const u of N.get(x)?.users || []) if (!up.has(u)){ up.add(u); st2.push(u); } }
  return new Set([...down, ...up]);
}
let selected = null;
function light(set, extra){
  const on = set ? (id => set.has(id)) : () => true;
  svg.classed("focus", !!set); litSet = set && set.size ? set : null; placeLabels();
  nodeSel.classed("on", d => on(d.id));
  branchSel.classed("on", e => on(e.t.id) && (!e.s || on(e.s.id)));
  shootSel.classed("on", e => on(e.t.id) && (!e.s || on(e.s.id))).attr("d", e => shootD(e, !!set || fullShoot(e)));
  leafSel.classed("on", f => on(f.d.id));
  pileSel.classed("on", p => extra === "pile:" + p.a);
  seedbed.classed("on", extra === "seedbed");
  roots.selectAll("path").classed("on", !!set && [...set].some(id => byId.get(id)?.up));
}
const tip = document.getElementById("tree-tip"), stage = document.getElementById("tree-box");
function showTip(ev, html){
  tip.innerHTML = html; tip.hidden = false;
  const r = stage.getBoundingClientRect(), x = ev.clientX - r.left, y = ev.clientY - r.top;
  tip.style.left = Math.min(r.width - 310, x + 14) + "px"; tip.style.top = (y + 16) + "px";
}
const hideTip = () => { tip.hidden = true; };
function statusLine(n){
  if (isUp(n)) return "upstream (BrownianMotion)";
  if (n.tw) return `tower of ${n.tw} modules · best hop ${n.hp ?? "∞"}`;
  if (isWood(n)) return (n.s === "partial" ? "proved in part" : "proved") + (n.e ? ` · ${n.e} corpus ${n.e === 1 ? "entry rests" : "entries rest"} here` : "")
    + (n.open.length ? ` · ${n.open.length} open ${n.open.length === 1 ? "issue" : "issues"}` : "");
  if (n.ph) return `connector · proving it brings ${n.ph.gain} more ${n.ph.gain === 1 ? "theorem" : "theorems"} within 3 hops` + (n.open.length ? " · " + n.open.map(x => "#" + x[0]).join(" ") : "");
  const bits = [n.op ? "open problem" : "frontier"]; if (n.core?.length) bits.push("core proved"); if (n.st) bits.push(STATUS_TXT[n.st]);
  if (n.seed || n.ground) bits.push("grows from upstream");
  return bits.join(" · ");
}
nodeSel.on("mouseenter", (ev, d) => { if (!selected) light(lineage(d.id)); showTip(ev, `<b>${esc(d.data.node.t)}</b>${esc(statusLine(d.data.node))}`); })
  .on("mousemove", (ev, d) => showTip(ev, `<b>${esc(d.data.node.t)}</b>${esc(statusLine(d.data.node))}`))
  .on("mouseleave", () => { hideTip(); if (!selected) light(null); })
  .on("click", (ev, d) => { ev.stopPropagation(); select(d.id); });
pileSel.on("mouseenter", (ev, p) => { if (!selected) light(new Set(), "pile:" + p.a); showTip(ev, `<b>${p.list.length} ${esc(pileName(p.a))} entries off the map</b>proved, but resting on no node and feeding none`); })
  .on("mousemove", (ev, p) => showTip(ev, `<b>${p.list.length} ${esc(pileName(p.a))} entries off the map</b>proved, but resting on no node and feeding none`))
  .on("mouseleave", () => { hideTip(); if (!selected) light(null); })
  .on("click", (ev, p) => { ev.stopPropagation(); selectPile(p.a); });
seedbed.on("mouseenter", ev => { if (!selected) light(new Set(), "seedbed"); showTip(ev, `<b>${upOnly} upstream-only entries</b>their proofs cite Mathlib and no MathFin constant`); })
  .on("mouseleave", () => { hideTip(); if (!selected) light(null); });
svg.on("click", () => { if (selected) select(null); });

// ---------- folio ----------
const folio = document.getElementById("tree-panel");
const chip = l => { const m = N.get(l); return m ? `<button class="chip${m.s === "frontier" ? " fr" : ""}" type="button" data-l="${esc(l)}">${esc(m.t)}</button>` : ""; };
const pill = (txt, v) => `<span class="pill"><i style="background:var(${v})"></i>${esc(txt)}</span>`;
function nodePanel(n){
  const d = byId.get(n.l);
  const kind = isUp(n) ? pill("upstream", "--tr-soil-ink") : n.ph ? pill("connector, not proved", "--tr-blue") : n.tw ? pill("tower", "--tr-bark") : isWood(n) ? pill(n.s === "partial" ? "proved in part" : "proved", "--tr-bark") : n.op ? pill("open problem", "--tr-star") : pill("frontier", "--tr-blue");
  const st = n.st ? pill(STATUS_TXT[n.st], STATUS_VAR[n.st]) : "";
  const iss = n.i.slice().sort((a, b) => (a[1] === "o" ? 0 : 1) - (b[1] === "o" ? 0 : 1) || b[0] - a[0]);
  const li = x => `<li><a class="num${x[1] === "o" ? "" : " closed"}" href="${GH}${x[0]}" target="_blank" rel="noopener">#${x[0]}</a><span class="${x[1] === "o" ? "" : "closed"}">${esc(x[3])}${x[2] ? " <span class='muted'>(PR)</span>" : ""}${x[1] === "o" && x[4][0] ? ` <span class="muted">· ${esc(STATUS_TXT[x[4][0]] || x[4][0])}</span>` : ""}${x[1] !== "o" ? " <span class='muted'>· closed</span>" : ""}</span></li>`;
  const uses = n.u.filter(u => N.has(u)), users = n.users;
  return `
    <button class="backbtn" type="button" data-back>← How to read the tree</button>
    <div style="display:flex; gap:6px; flex-wrap:wrap">${kind}${st}<span class="pill">${esc(cellName(cellKey(n)))}</span>${n.f && FAM.get(n.f) ? `<span class="pill"><i style="background:${famVar(n)}"></i>${esc(FAM.get(n.f).title)}</span>` : ""}${isJoint(n) ? `<span class="pill">joint · ${esc(n.j.map(partTitle).join(" and "))}</span>` : ""}</div>
    <h2>${esc(n.t)}</h2>
    ${n.x ? `<p class="stmt">${prose(n.x)}</p>` : ""}
    ${n.ph ? `<div><h3>Connector</h3><p>A theorem stated in MathFinFrontier and closed by <code>sorry</code>. Proved, it would bring <b>${n.ph.gain}</b> more finance ${n.ph.gain === 1 ? "theorem" : "theorems"} within 3 statement hops of the trunk${n.hp ? `, and it would itself sit at hop ${n.hp}` : ""}.${n.open.length ? " Issue " + n.open.map(x => `<a href="${GH}${x[0]}" target="_blank" rel="noopener">#${x[0]}</a>`).join(", ") + "." : ""}</p></div>` : ""}
    ${!n.ph && n.hp != null && kindOf(n) === "limb" ? `<div><h3>Distance from the trunk</h3><p>Hop ${n.hp}: ${n.hp === 1 ? "its statement mentions the trunk itself" : `its statement mentions an object ${n.hp - 1} ${n.hp === 2 ? "statement" : "statements"} from the trunk`}.</p></div>` : ""}
    ${n.isl ? `<div><h3>Island</h3><p>No statement joins this to the trunk (infinite hop). ${(D.islands.find(c => c.key === n.isl) || {}).declared ? "Declared standalone: " + esc(D.islands.find(c => c.key === n.isl).reason) : "A connector or a declared reason is missing."}</p></div>` : ""}
    ${n.d ? `<div><h3>Lean</h3><div class="mono">${n.h ? `<a href="${esc(n.h)}">${esc(n.d)}</a>` : esc(n.d)}</div>${n.m ? `<div class="muted" style="font-size:12.5px">${esc(n.m)}</div>` : ""}</div>` : ""}
    ${isWood(n) ? `<div><h3>Corpus</h3><p>${n.e ? `<b>${n.e}</b> ${n.e === 1 ? "entry hangs" : "entries hang"} here as leaves: this is the deepest node ${n.e === 1 ? "its proof rests" : "their proofs rest"} on.` : "No entry has this as its deepest node; entries reach it through the nodes above."}</p></div>` : ""}
    ${n.core?.length ? `<div><h3>Core already proved</h3><ul class="entries">${n.core.map(c => `<li><span class="mono">${esc(c)}</span></li>`).join("")}</ul></div>` : ""}
    ${n.sucker && isWood(n) ? `<div><h3>Rests on Mathlib alone</h3><p>No blueprint node is in its proof term, so it grows from the soil in its sector of the map rather than from the trunk or a root. If its mathematics does build on a library object, tagging that object or proving the bridge lifts it into the crown.</p></div>` : ""}
    ${n.ground ? `<div><h3>Grows from upstream</h3><p>${esc(n.ground)}</p></div>` : ""}
    ${uses.length ? `<div><h3>Rests on</h3><div class="chips">${uses.map(chip).join("")}</div></div>` : ""}
    ${users.length ? `<div><h3>What grows from it</h3><div class="chips">${users.map(chip).join("")}</div></div>` : ""}
    ${iss.length ? `<div><h3>Issues and pull requests</h3><ul class="issues">${iss.map(li).join("")}</ul></div>` : ""}
    <div class="muted mono" style="font-size:11.5px">${esc(n.l)}</div>`;
}
function glyph(kind){
  const s = {
    knot:`<path class="branch" d="M2,20 C10,16 18,12 28,6 L29,8 C19,14 11,18 3,22Z"/><circle class="knot" cx="28" cy="7" r="4"/>`,
    leaf:`<path class="leaf l1" d="${LEAF}" transform="translate(6,14) rotate(-20) scale(1.6)"/><path class="leaf l3" d="${LEAF}" transform="translate(14,16) rotate(25) scale(1.3)"/>`,
    bud:`<path class="shoot" d="M2,22 C12,18 18,12 26,8"/><circle class="bud" cx="27" cy="8" r="4.6"/><circle class="bud-dot st-ready" cx="27" cy="8" r="1.7"/>`,
    core:`<circle class="bud" cx="17" cy="12" r="6"/><path class="bud-core" d="M17,6 A6,6 0 0 0 17,18 Z"/>`,
    star:`<circle class="halo" cx="17" cy="12" r="11"/><path class="star" transform="translate(17,12)" d="M${STAR(7.5).join("L")}Z"/>`,
    fallen:`<path class="fallen" d="${LEAF}" transform="translate(4,16) rotate(-8) scale(1.5)"/><path class="fallen" d="${LEAF}" transform="translate(16,19) rotate(160) scale(1.2)"/><line x1="0" x2="34" y1="21" y2="21" class="ground-line"/>`,
    sucker:`<rect x="0" y="18" width="34" height="8" class="soil-1"/><path class="branch" d="M7,22 C8,14 13,10 18,7 L19,8.5 C14,12 10,15 9.5,22Z"/><circle class="knot" cx="19" cy="7" r="3.6"/>`,
    seed:`<rect x="0" y="18" width="34" height="8" class="soil-1"/><path class="shoot" d="M8,22 C10,14 16,10 20,6"/><circle class="bud" cx="20" cy="6" r="4.2"/><circle class="bud-dot st-ready" cx="20" cy="6" r="1.6"/>`,
    ghost:`<path class="ghost" style="opacity:1" d="M4,23 C10,14 14,10 30,4 L31,8 C17,13 14,17 11,23Z"/>`,
    fam:`<circle class="knot" cx="7" cy="12" r="4.5" style="fill:var(--fam-diffusions)"/><circle class="knot" cx="17" cy="12" r="4.5" style="fill:var(--fam-default)"/><circle class="knot" cx="27" cy="12" r="4.5" style="fill:var(--fam-jumps)"/>`,
    hop:`<line x1="6" x2="6" y1="22" y2="3" class="ground-line" style="opacity:1"/><circle class="knot" cx="6" cy="20" r="2.6"/><circle class="knot" cx="6" cy="12" r="2.6"/><circle class="knot" cx="6" cy="5" r="2.6"/><text x="12" y="22" font-size="8" fill="currentColor">1</text><text x="12" y="6" font-size="8" fill="currentColor">3</text>`,
    issring:`<circle class="knot" cx="17" cy="12" r="4"/><circle class="iss-ring" cx="17" cy="12" r="7.5" style="stroke:var(--tr-ready)"/>`,
    island:`<ellipse class="isl-ring ring" cx="17" cy="12" rx="15" ry="9"/><circle class="knot" cx="12" cy="12" r="3"/><circle class="knot" cx="21" cy="11" r="3"/>`,
    tower:`<rect class="knot tower" x="8" y="3" width="18" height="18" rx="3"/><text x="17" y="16" text-anchor="middle" font-size="9" font-weight="700" fill="var(--surface)">9</text>`,
    phantom:`<path class="shoot ph" d="M3,20 Q10,2 17,8"/><path class="shoot ph" d="M31,20 Q24,2 17,8"/><circle class="phantom" cx="17" cy="9" r="6"/>`,
    vein:`<path class="vein on" style="opacity:.6" d="M2,20 Q17,4 32,20"/>`
  }[kind];
  return `<svg viewBox="0 0 34 24" aria-hidden="true">${s}</svg>`;
}
function dots(){ return Object.entries({"ready to pick up":"--tr-ready","in progress":"--tr-progress",research:"--tr-research",blocked:"--tr-blocked"}).map(([t, v]) => `<span class="pill"><i style="background:var(${v})"></i>${t}</span>`).join(" "); }
function defaultPanel(){
  const ops = D.nodes.filter(n => n.op);
  const ready = D.nodes.filter(n => n.s === "frontier" && n.st === "ready" && !n.op);
  folio.innerHTML = `
    <h2>How to read the tree</h2>
    <h3>Always on the tree</h3>
    <div class="legend">
      <div>${glyph("ghost")}<span><b>The map</b>, in pale wood, is docs/taxonomy.toml: the tools as roots (probability in its branches, statistics), positions and markets as the trunk, and three limbs, one for each question asked of a position (choice, valuation, risk). A node's place on it is a reading, not a proof.</span></div>
      <div>${glyph("hop")}<span><b>Height is measured</b>: on a limb a node sits at its hop, its distance in statements from the trunk (the metric of <code>chain_reach</code>). Probability tools stay in the roots.</span></div>
      <div>${glyph("knot")}<span><b>Dark wood and knots</b>: the proved blueprint nodes and the main use each proof makes; select a node to see all of them. Wood thickens with the corpus it carries; a knot's size counts the corpus entries resting deepest on it.</span></div>
      <div>${glyph("fam")}<span><b>Colour</b> is the model family, the same hue in every limb; a node in wood colour is general theory. A <b>joint</b> sits in the fork between the two limbs its statement joins.</span></div>
      <div>${glyph("tower")}<span><b>Towers</b> are single nodes, the module count inside.</span></div>
      <div>${glyph("sucker")}<span><b>Stems from the soil</b>: proved nodes off the roots that rest on no blueprint node, only on Mathlib.</span></div>
    </div>
    <h3>Gaps</h3>
    <div class="legend">
      <div>${glyph("island")}<span><b>Islands</b>: proved nodes at infinite distance float beside their limb; a red ring means no connector reaches them and no standalone reason is declared.</span></div>
      <div>${glyph("phantom")}<span><b>Connectors</b>: hollow dashed dots between the nodes a stated, not yet proved theorem would join; the number is how many theorems proving it brings within 3 hops.</span></div>
    </div>
    <h3>Future work</h3>
    <div class="legend">
      <div>${glyph("bud")}<span><b>Buds</b>: unproved blueprint nodes, each carried by an open issue and joined to the proved node it rests on; the centre shows the issue's state.</span></div>
      <div>${glyph("issring")}<span><b>Ringed knots</b>: proved nodes an open issue works on (a refactor, an upgrade, a generalisation), ringed in the issue's state.</span></div>
      <div>${glyph("core")}<span><b>Half-filled bud</b>: its core is already proved in the corpus.</span></div>
      <div>${glyph("seed")}<span><b>Seedlings</b>: future work that grows straight from Mathlib or BrownianMotion.</span></div>
    </div>
    <h3>Open problems</h3>
    <div class="legend">
      <div>${glyph("star")}<span><b>Stars</b>: open problems of the field, statements nobody has proved, carried by an issue labelled open-problem.</span></div>
    </div>
    <h3>Leaves</h3>
    <div class="legend">
      <div>${glyph("leaf")}<span><b>Leaves</b>: the corpus entries, hung on the deepest node their proof rests on.</span></div>
      <div>${glyph("fallen")}<span><b>Fallen leaves</b>: proved entries that rest on no node; each one is a missing tag or bridge.</span></div>
    </div>
    <div class="chips">${dots()}</div>
    <div><h3>Open problems</h3><div class="chips">${ops.map(n => chip(n.l)).join("")}</div></div>
    <div><h3>Ready to pick up · ${ready.length}</h3><div class="chips">${ready.sort((a, b) => a.t.localeCompare(b.t)).slice(0, 14).map(n => chip(n.l)).join("")}${ready.length > 14 ? ` <span class="muted" style="font-size:12.5px; align-self:center">and ${ready.length - 14} more on the tree</span>` : ""}</div></div>`;
}
function selectPile(a){
  selected = "pile:" + a; light(new Set(), selected); selRing.attr("visibility", "hidden");
  const list = piles.find(p => p.a === a)?.list || [];
  folio.innerHTML = `<button class="backbtn" type="button" data-back>← How to read the tree</button>
    <span class="pill"><i style="background:var(--tr-fallen)"></i>off the map</span>
    <h2>${list.length} ${esc(pileName(a))} entries on the ground</h2>
    <p>Proved and imported by the library, but no constant they cite reaches a blueprint node, and no node depends on them. A tag on the object they share, or a bridge to the node they illustrate, lifts them onto the tree.</p>
    <ul class="entries">${list.map(([id, name, c]) => `<li>${esc(name)}<br><span class="mono">${esc(id)}</span>${PARTS.has(a) ? ` <span class="muted">· ${esc(c)}</span>` : ""}</li>`).join("")}</ul>`;
}
function select(l){
  selected = l; hideTip();
  if (!l){ light(null); selRing.attr("visibility", "hidden"); defaultPanel(); return; }
  const d = byId.get(l); if (!d) return;
  light(lineage(l)); selRing.attr("cx", d.px).attr("cy", d.py).attr("visibility", "visible");
  folio.innerHTML = nodePanel(N.get(l)); folio.scrollTop = 0;
}
folio.addEventListener("click", e => {
  const b = e.target.closest("[data-l]"); if (b){ const d = byId.get(b.dataset.l); select(b.dataset.l); if (d) focusOn(d); return; }
  if (e.target.closest("[data-back]")) select(null);
});

// ---------- search ----------
const q = document.getElementById("t-q");
const matches = s => { s = s.trim().toLowerCase(); if (!s) return [];
  return D.nodes.filter(n => (n.t + " " + n.l + " " + (n.d || "")).toLowerCase().includes(s)); };
q.addEventListener("input", () => { if (selected) return; const m = matches(q.value);
  if (!q.value.trim()) return light(null); light(new Set(m.map(n => n.l))); });
q.addEventListener("keydown", e => { if (e.key !== "Enter") return; const m = matches(q.value); if (!m.length) return;
  m.sort((a, b) => (b.s !== "frontier") - (a.s !== "frontier")); select(m[0].l); const d = byId.get(m[0].l); if (d) focusOn(d); });

// ---------- layers on demand ----------
for (const b of document.querySelectorAll("#tree-box [data-layer]")){
  const set = on => { b.setAttribute("aria-pressed", on); svg.classed("show-" + b.dataset.layer, on); };
  set(b.getAttribute("aria-pressed") === "true");
  b.onclick = () => { set(b.getAttribute("aria-pressed") !== "true"); light(litSet); };
}

// ---------- growth ----------
const reduce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
const growBtn = document.getElementById("t-grow");
if (reduce) growBtn.hidden = true;
function lvl(d){ return d ? (d.depth ?? 0) : 0; }
growBtn.onclick = () => {
  select(null);
  const step = 260, dur = 420;
  const fade = (sel, delay) => sel.interrupt().style("opacity", 0).transition().delay(delay).duration(dur).style("opacity", null);
  fade(view.select(".map-ghost"), 0);
  fade(branchSel, e => 160 + (e.t.depth + 1) * step); fade(nodeSel.filter(d => d.up || isWood(d.data.node)), d => 220 + (d.depth + 1) * step);
  fade(leafSel, f => 340 + (f.d.depth + 1) * step + f.k * 5);
  const last = 340 + (d3.max(nodeData, d => d.depth) + 1) * step;
  fade(pileSel, last + 150);
  fade(shootSel, e => last + 250 + e.t.depth * 160);
  fade(nodeSel.filter(d => !d.up && !isWood(d.data.node)), d => last + 400 + d.depth * 160);
};

defaultPanel();
placeLabels(1);
})();
