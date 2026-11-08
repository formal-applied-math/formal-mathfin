/* The program tree (tree.html): the blueprint drawn as a tree, grown from Mathlib and
 BrownianMotion. Height is conceptual depth: a node sits above everything it rests on, Foundations
 is the trunk, every use is drawn as wood, and wood thickens with the corpus it carries; the use
 that sets a node's height is drawn in bark, the others lighter. Corpus entries are leaves on the
 deepest node their proof rests on; off-map entries lie on the ground. Labels are sized in screen
 pixels and fill in with zoom. Data: the JSON block #tree-data, written by tools/verify/docs_site.py
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
const AREA_TXT = {foundations:"foundations","black-scholes":"Black–Scholes","fixed-income":"fixed income",portfolio:"portfolio",risk:"risk",actuarial:"actuarial","stoch-vol":"stochastic vol",defi:"DeFi",binomial:"binomial",credit:"credit",contracts:"contracts",execution:"execution",futures:"futures",fx:"FX",commodities:"commodities",upstream:"upstream"};
const areaName = a => AREA_TXT[a] || a;
// statement prose: TeX between dollars is typeset (KaTeX, MathML output: no stylesheet or fonts to fetch);
// outside it, `code` and *emphasis* are the blueprint's own markup
const tex = m => { try { return window.katex.renderToString(m, {throwOnError:false}); } catch (e) { return esc("$" + m + "$"); } };
const prose = t => String(t ?? "").split(/(\$[^$]*\$)/).map((seg, i) => i % 2 ? tex(seg.slice(1, -1))
  : esc(seg).replace(/`([^`]+)`/g, "<code>$1</code>").replace(/\*([^*\s][^*]*)\*/g, "<em>$1</em>")).join("");

for (const n of D.nodes){
  n.users = [];
  n.open = n.i.filter(x => x[1] === "o");
  const sts = n.open.map(x => x[4][0] || "ready");
  n.st = n.s === "frontier" ? (STATUS_RANK.find(s => sts.includes(s)) || (n.open.length ? "ready" : null)) : null;
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

// ---------- layout: height is conceptual depth, Foundations is the trunk ----------
const W = 1600, CX = 800, GY = 890, LH = 124, Y0 = GY - 240;
const pxPerUnit = () => (document.getElementById("tree").getBoundingClientRect().width || W) / W;
// the plate's fixed captions (areas, strata, piles) are drawn for a ~1300px stage; on a narrower one they grow, up to 1.7×
const TF = Math.min(1.7, Math.max(1, .8 / pxPerUnit()));
const cap = (sel, px) => sel.style("font-size", (px * TF).toFixed(1) + "px");
// the soil, top down: the rows of pile labels, the BrownianMotion stratum, the Mathlib stratum; it deepens with its captions
const ROW0 = GY + 10 + 14 * TF, ROWH = 17 * TF, BM_Y = ROW0 + ROWH + 30 * TF, M_TOP = BM_Y + 34 * TF, M_Y = M_TOP + 32 * TF;
const H = Math.round(M_Y + 52 * TF);
const live = D.nodes.filter(n => !isUp(n));
for (const n of live) n.depth = depth(n.l);
const maxLevel = d3.max(live, n => n.depth);
const mfUses = n => n.u.filter(u => N.has(u));
// a node with no blueprint use rests on Mathlib directly: a sucker from the soil, unless it is Foundations
for (const n of live) n.sucker = !mfUses(n).length && n.a !== "foundations";

// corpus flow: what each node carries, split evenly among the nodes it rests on
const own = n => isWood(n) ? 1 + n.e : .45;
const flow = new Map();
for (const n of live.slice().sort((x, y) => y.depth - x.depth)){
  let f = own(n);
  for (const m of n.users){ const mm = N.get(m); if (mm && !isUp(mm)) f += (flow.get(m) || 0) / mfUses(mm).length; }
  flow.set(n.l, f);
}
for (const n of D.nodes.filter(isUp)) flow.set(n.l, n.users.reduce((s, m) => s + flow.get(m) / mfUses(N.get(m)).length, 0));

// area columns: Foundations in the middle, the applications to either side, the crown widening as it climbs
const LEFT = ["portfolio", "risk", "actuarial", "credit", "defi", "execution"];
const RIGHT = ["black-scholes", "stoch-vol", "binomial", "contracts", "futures", "commodities", "fixed-income", "fx"];
const count = a => live.filter(n => n.a === a).length;
const colX = new Map([["foundations", CX]]);
for (const [side, list] of [[-1, LEFT], [1, RIGHT]]){
  const present = list.filter(a => count(a)); const ws = present.map(a => Math.pow(count(a), .62));
  const tot = d3.sum(ws); let acc = 0;
  present.forEach((a, i) => { colX.set(a, CX + side * (210 + (acc + ws[i] / 2) / tot * 520)); acc += ws[i]; });
}
for (const n of live) if (!colX.has(n.a)) colX.set(n.a, CX + 640);
const widen = lv => .62 + .38 * lv / Math.max(1, maxLevel);
const yTarget = n => n.sucker ? GY - 78 - hash(n.l) * 70
  : n.depth === 0 && n.a === "foundations" ? GY - 150 - hash(n.l) * 120
  : Y0 - (n.depth - (n.depth ? .55 : 0)) * LH;
const xTarget = n => n.a === "foundations" ? CX + (hash(n.l + "f") - .5) * (70 + n.depth * 70) : CX + (colX.get(n.a) - CX) * (n.sucker ? 1.02 : widen(n.depth));
const rad = n => isWood(n) ? 11 + Math.sqrt(n.e) * 2.9 : n.op ? 15 : 9;
const sim = live.map(n => ({id:n.l, n, x:xTarget(n) + (hash(n.l + "x") - .5) * 60, y:yTarget(n)}));
const linkData = [];
for (const n of live) for (const u of mfUses(n)) if (!isUp(N.get(u))) linkData.push({source:u, target:n.l});
d3.forceSimulation(sim)
  .force("x", d3.forceX(s => xTarget(s.n)).strength(s => s.n.a === "foundations" ? .16 : .3))
  .force("y", d3.forceY(s => yTarget(s.n)).strength(.85))
  .force("link", d3.forceLink(linkData).id(s => s.id).distance(LH).strength(.035))
  .force("collide", d3.forceCollide(s => rad(s.n)).strength(.9).iterations(3))
  .stop().tick(420);

const byId = new Map();
for (const s of sim){
  const n = s.n;
  byId.set(n.l, {id:n.l, data:{node:n}, px:Math.max(70, Math.min(W - 70, s.x)), py:Math.max(84, Math.min(GY - 54, s.y)),
    depth:n.depth, value:flow.get(n.l), seed:n.s === "frontier" && !mfUses(n).length});
}
const upNodes = D.nodes.filter(isUp);
upNodes.forEach((n, k) => byId.set(n.l, {id:n.l, data:{node:n}, px:CX + 70 + k * 90, py:ROW0 + ROWH - 5, up:true, depth:-1, value:flow.get(n.l)}));

// the primary parent is the deepest node a node rests on (it sets the height); the other uses are drawn lighter
for (const n of live){
  const us = mfUses(n).filter(u => !isUp(N.get(u)));
  n.prim = us.length ? us.reduce((a, b) => (N.get(b).depth - N.get(a).depth || flow.get(b) - flow.get(a)) > 0 ? b : a) : null;
}
// edges: every use, drawn from the node it rests on up to the node that uses it
const edges = [];
for (const n of live){
  const t = byId.get(n.l), us = mfUses(n);
  for (const u of us) edges.push({s:byId.get(u), t, f:flow.get(n.l) / us.length, prim:u === n.prim || (!n.prim && isUp(N.get(u)))});
  if (!us.length){
    const r = hash(n.l + "stem");
    const base = n.a === "foundations" ? [CX + (r - .5) * 22, GY + 6] : [t.px + (r - .5) * 26, GY + 6];
    edges.push({s:null, base, t, f:flow.get(n.l), prim:true});
  }
}
for (const e of edges){ if (e.s && e.s.up) e.base = [CX + (hash(e.t.id) - .5) * 16, GY + 6]; }
const BW = f => Math.min(26, .9 + 1.32 * Math.sqrt(f));
function dirOf(d){
  const n = d.data?.node; if (!n || d.up) return [0, -1];
  const ps = mfUses(n).map(u => byId.get(u)).filter(x => x && !x.up);
  const [mx, my] = ps.length ? [d3.mean(ps, p => p.px), d3.mean(ps, p => p.py)] : [n.a === "foundations" ? CX : d.px, GY];
  let v = [d.px - mx, d.py - my]; const l = Math.hypot(...v) || 1; v = [v[0] / l * .7, Math.min(-.35, v[1] / l)];
  const m = Math.hypot(...v); return [v[0] / m, v[1] / m];
}
const areaX = new Map();
for (const a of new Set(D.nodes.map(n => n.a))){
  const xs = [...byId.values()].filter(d => !d.up && d.data.node.a === a && isWood(d.data.node)).map(d => d.px);
  if (xs.length) areaX.set(a, d3.median(xs));
}

// ---------- drawing ----------
const svg = d3.select("#tree").attr("viewBox", `0 0 ${W} ${H}`).style("aspect-ratio", `${W} / ${H}`);
const view = svg.append("g");

// soil strata
const ground = view.append("g");
const wave = (y, amp, ph) => d3.range(0, W + 41, 40).map(x => [x, y + Math.sin(x / 190 + ph) * amp]);
const area = (top, bot) => d3.area().x(p => p[0]).y0(p => p[1]).y1(bot).curve(d3.curveBasis)(top);
ground.append("path").attr("class", "soil-1").attr("d", area(wave(GY, 4, 0), H));
ground.append("path").attr("class", "soil-2").attr("d", area(wave(M_TOP, 5, 1.7), H));
ground.append("path").attr("class", "ground-line").attr("d", d3.line().curve(d3.curveBasis)(wave(GY, 4, 0)));
cap(ground.append("text").attr("class", "stratum").attr("x", 30).attr("y", BM_Y).text("BrownianMotion"), 15);
cap(ground.append("text").attr("class", "stratum").attr("x", 30).attr("y", M_Y).text("Mathlib"), 15);
cap(ground.append("text").attr("class", "stratum-sub").attr("x", 30).attr("y", BM_Y + 20 * TF).text("Brownian motion, stochastic integration"), 16);
cap(ground.append("text").attr("class", "stratum-sub").attr("x", 30).attr("y", M_Y + 20 * TF).text("measure, probability, analysis, linear algebra"), 16);
{ const r = rng("stones"); for (let k = 0; k < 70; k++){
  const x = r() * W, y = M_TOP + 12 + r() * (H - M_TOP - 20);
  if (x < 40 + 400 * TF && y < M_Y + 30 * TF) continue;
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
// the trunk: everything that rises from Brownian motion or from Mathlib through Foundations
const trunkFlow = d3.sum(edges.filter(e => (e.s === null && e.t.data.node.a === "foundations") || (e.s && e.s.up)), e => e.f);
const TW = Math.min(72, 8 + 1.5 * Math.sqrt(trunkFlow));
const TTOP = GY - 150;
const roots = view.append("g");
{ const r = rng("roots"); const spec = [[-1,.9,62],[-.55,.6,100],[-.2,.35,120],[.25,.4,112],[.6,.65,96],[1,.95,70],[-.8,.2,150],[.85,.25,140]];
  for (const [dir, spread, depthR] of spec){
    const P = [CX + dir * TW * .3, GY - 6], C = [CX + dir * (110 + spread * 230) + (r() - .5) * 40, GY + depthR * (0.5 + r() * .4)];
    roots.append("path").attr("class", "root dimmable").attr("d", taper(P, [P[0] + dir * 20, GY + 14], [C[0] - dir * 60, C[1] - 18], C, TW * .3, .8));
  } }
view.append("path").attr("class", "trunk dimmable")
  .attr("d", `M${CX - TW * .9},${GY + 6} C${CX - TW * .5},${GY - 24} ${CX - TW * .46},${GY - 70} ${CX - TW * .36},${TTOP}
              L${CX + TW * .36},${TTOP} C${CX + TW * .46},${GY - 70} ${CX + TW * .5},${GY - 24} ${CX + TW * .9},${GY + 6} Z`);
view.append("text").attr("class", "trunk-lbl").attr("transform", `translate(${CX + 4},${GY - 14}) rotate(-90)`).text("foundations");

const linkG = view.append("g"), shootG = view.append("g");
function edgeGeom(e){
  const P = e.s && !e.s.up ? [e.s.px, e.s.py] : e.base, C = [e.t.px, e.t.py], dy = Math.max(30, P[1] - C[1]);
  return {P, c1:[P[0], P[1] - dy * .55], c2:[C[0], C[1] + dy * .42], C};
}
const woodEdges = edges.filter(e => isWood(e.t.data.node)).sort((a, b) => b.f - a.f);
const shootEdges = edges.filter(e => !isWood(e.t.data.node));
const branchSel = linkG.selectAll("path").data(woodEdges.slice().sort((a, b) => a.prim - b.prim || b.f - a.f)).join("path").attr("class", e => "branch dimmable" + (e.prim ? "" : " sec"))
  .attr("d", e => { const g = edgeGeom(e), w = BW(e.f); return taper(g.P, g.c1, g.c2, g.C, w * 1.15, Math.max(.8, w * .62)); });
const shootSel = shootG.selectAll("path").data(shootEdges).join("path").attr("class", e => "shoot dimmable" + (e.prim ? "" : " sec"))
  .attr("d", e => { const g = edgeGeom(e); return `M${g.P}C${g.c1} ${g.c2} ${g.C}`; });

// area names: one row across the top of the plate, each with a faint guide down to its part of the crown
const limbLbl = view.append("g").attr("class", "dimmable"), areaLbls = [];
for (const a of colX.keys()){
  if (a === "foundations") continue;
  const ds = [...byId.values()].filter(d => !d.up && d.data.node.a === a && !d.data.node.sucker);
  if (ds.length < 3) continue;
  const name = areaName(a);
  const all = live.filter(n => n.a === a), np = all.filter(isWood).length, cnt = `${np} proved · ${all.length - np} frontier`;
  areaLbls.push({a, x:d3.median(ds, d => d.px), top:d3.min(ds, d => d.py), w:(Math.max(name.length * 11.6, cnt.length * 6.9) + 22) * TF, name, cnt});
}
areaLbls.sort((p, q) => p.x - q.x);
for (let it = 0; it < 60; it++){            // relax: push overlapping neighbours apart symmetrically
  let moved = false;
  for (let i = 1; i < areaLbls.length; i++){
    const p = areaLbls[i - 1], q = areaLbls[i], need = (p.w + q.w) / 2 - (q.x - p.x);
    if (need > 0){ p.x -= need / 2; q.x += need / 2; moved = true; }
  }
  for (const L of areaLbls) L.x = Math.max(L.w / 2 + 12, Math.min(W - L.w / 2 - 12, L.x));
  if (!moved) break;
}
const LROW = 12 + 18 * TF;
// too many for one row: stagger alternate names onto a second row and relax each row on its own
if (d3.sum(areaLbls, L => L.w) > W - 60){
  areaLbls.forEach((L, i) => { L.row = i % 2; });
  for (let it = 0; it < 60; it++) for (const r of [0, 1]){
    const row = areaLbls.filter(L => L.row === r);
    for (let i = 1; i < row.length; i++){ const p = row[i - 1], q = row[i], need = (p.w + q.w) / 2 - (q.x - p.x); if (need > 0){ p.x -= need / 2; q.x += need / 2; } }
    for (const L of row) L.x = Math.max(L.w / 2 + 12, Math.min(W - L.w / 2 - 12, L.x));
  }
} else areaLbls.forEach(L => { L.row = 0; });
for (const L of areaLbls){
  const y = LROW + L.row * 44 * TF;
  const ds = [...byId.values()].filter(d => !d.up && d.data.node.a === L.a && !d.data.node.sucker), cx = d3.median(ds, d => d.px);
  limbLbl.append("path").attr("class", "limb-guide").attr("d", `M${L.x},${y + 24 * TF}C${L.x},${y + 70} ${cx},${L.top - 60} ${cx},${L.top - 18}`);
  cap(limbLbl.append("text").attr("class", "limb-lbl").attr("x", L.x).attr("y", y).attr("text-anchor", "middle").text(L.name), 14.5);
  cap(limbLbl.append("text").attr("class", "limb-n").attr("x", L.x).attr("y", y + 17 * TF).attr("text-anchor", "middle").text(L.cnt), 12.5);
}

// leaves: one per corpus entry resting on the node
const leafG = view.append("g").attr("display", "none");
const LEAF = "M0,0 C2.2,-2.6 5.6,-2.6 8,0 C5.6,2.6 2.2,2.6 0,0Z";
const leafData = [];
for (const d of byId.values()){
  const n = d.data.node; if (d.up || !n.e) continue;
  const r = rng(n.l), [ux, uy] = dirOf(d), base = Math.atan2(uy, ux);
  for (let k = 0; k < n.e; k++){
    const a = base + (r() - .5) * 3.3, rr = 5 + Math.sqrt(r()) * (9 + Math.sqrt(n.e) * 4.4);
    leafData.push({d, x:d.px + Math.cos(a) * rr, y:d.py + Math.sin(a) * rr, rot:a * 180 / Math.PI + (r() - .5) * 70, s:1.15 + r() * .7, c:1 + Math.floor(r() * 3), k});
  }
}
const leafSel = leafG.selectAll("path").data(leafData).join("path")
  .attr("class", f => `leaf l${f.c} dimmable`).attr("d", LEAF)
  .attr("transform", f => `translate(${f.x.toFixed(1)},${f.y.toFixed(1)}) rotate(${f.rot.toFixed(0)}) scale(${f.s.toFixed(2)})`);

// fallen leaves: proved entries off the map, under their area
const litterG = view.append("g");
const piles = Object.entries(D.off).map(([a, list]) => ({a, list}));
const pileX = new Map(); { const used = [{x:CX, half:TW * .9 + 6}];
  for (const p of piles.sort((x, y) => y.list.length - x.list.length)){
    let x = areaX.get(p.a) ?? colX.get(p.a) ?? W - 150; const half = 14 + Math.sqrt(p.list.length) * 6.5;
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
  cap(g.append("text").attr("class", "pile-lbl").attr("x", x).attr("y", ROW0).text(`${p.list.length} ${areaName(p.a)}`), 13.5);
  g.append("rect").attr("class", "hit").attr("x", x - half - 8).attr("y", GY - 18).attr("width", 2 * half + 16).attr("height", 24 + 20 * TF);
});
// pile labels, measured: the first row with room, else the next one down (the upstream node's name holds a slot in the second)
{ const rows = [[], [], []], pad = 8 * TF;
  for (const u of upNodes){ const d = byId.get(u.l), hw = u.t.length * 4.6 * TF + pad; rows[1].push({x:d.px + 18 + hw, lw:hw}); }
  const lbls = []; pileSel.each(function(p){ const t = d3.select(this).select(".pile-lbl"); lbls.push({t, x:pileX.get(p.a).x, lw:t.node().getComputedTextLength() / 2 + pad}); });
  for (const L of lbls.sort((a, b) => a.x - b.x)){
    const r = Math.max(0, rows.findIndex(row => !row.some(u => Math.abs(u.x - L.x) < u.lw + L.lw)));
    rows[r].push(L); L.t.attr("y", ROW0 + r * ROWH);
  } }
// upstream-only entries as seeds in the Mathlib stratum
const upOnly = Object.values(D.areas).reduce((s, c) => s + (c["upstream-only"] || 0), 0);
const seedbed = view.append("g").attr("class", "seedbed dimmable");
{ const r = rng("seedbed"), x0 = W - 330;
  for (let k = 0; k < upOnly; k++) seedbed.append("ellipse").attr("class", "seedmark").attr("cx", x0 + r() * 270).attr("cy", M_TOP + 22 + r() * (H - M_TOP - 50)).attr("rx", 2.4).attr("ry", 1.5).attr("transform-origin", "center");
  cap(seedbed.append("text").attr("class", "stratum-sub").attr("x", x0 + 270).attr("y", H - 14).attr("text-anchor", "end").text(`${upOnly} entries cite Mathlib alone`), 16);
  seedbed.append("rect").attr("class", "hit").attr("x", x0 - 6).attr("y", M_TOP + 10).attr("width", 282).attr("height", H - M_TOP - 10); }

// nodes
const nodeG = view.append("g");
const nodeData = [...byId.values()].filter(d => d.data && d.data.node);
const STAR = (r) => d3.range(12).map(i => { const a = -Math.PI / 2 + i * Math.PI / 6, rr = i % 2 ? r * .45 : r; return [Math.cos(a) * rr, Math.sin(a) * rr]; });
const isOP = n => !!n.op;
const nodeSel = nodeG.selectAll("g").data(nodeData).join("g").attr("class", "nd dimmable").attr("transform", d => `translate(${d.px},${d.py})`);
nodeSel.each(function(d){
  const g = d3.select(this), n = d.data.node;
  if (d.up){ g.append("ellipse").attr("rx", 11).attr("ry", 6.5).attr("class", "knot"); cap(g.append("text").attr("class", "stratum-sub").attr("x", 18).attr("y", 5).text(n.t), 16); }
  else if (isWood(n)){ g.append("circle").attr("r", 2.6 + Math.min(6.4, Math.sqrt(n.e) * 1.05)).attr("class", "knot" + (n.s === "partial" ? " partial" : "")); }
  else if (isOP(n)){ g.append("circle").attr("r", 13).attr("class", "halo"); g.append("path").attr("class", "star").attr("d", "M" + STAR(7.5).join("L") + "Z"); }
  else {
    g.append("circle").attr("r", 4.6).attr("class", "bud");
    if (n.core && n.core.length) g.append("path").attr("class", "bud-core").attr("d", "M0,-4.6 A4.6,4.6 0 0 0 0,4.6 Z");
    g.append("circle").attr("r", 1.7).attr("cx", n.core && n.core.length ? 1.9 : 0).attr("class", "bud-dot st-" + (n.st || "none"));
  }
  g.append("circle").attr("r", d.up ? 14 : 9).attr("class", "hit");
});

// labels: sized in screen pixels, tried at four spots around the node, never over a knot or another label
const lblG = view.append("g");
function shortTitle(t, max){ let s = t.replace(/\s*\(.*?\)\s*/g, " ").replace(/\s+—.*$/, "").replace(/:.*$/, "").trim(); return s.length > max ? s.slice(0, max - 1).trimEnd() + "…" : s; }
const lblData = nodeData.filter(d => !d.up).map(d => {
  const n = d.data.node, [ux, uy] = d.seed ? [0, -1] : dirOf(d);
  const side = Math.abs(ux) < .28 ? 0 : (ux < 0 ? -1 : 1);
  const pr = isOP(n) ? 1e6 : isWood(n) ? d.value * 10 + n.e : (n.st === "ready" ? 3 : 1);
  return {d, n, side, pr, full: shortTitle(n.t, 46), short: shortTitle(n.t, 34)};
});
const lblSel = lblG.selectAll("text").data(lblData).join("text")
  .attr("class", L => "lbl dimmable" + (isOP(L.n) ? " op" : !isWood(L.n) ? " fr" : ""));
const glyphR = d => { const n = d.data.node; return isWood(n) ? 2.6 + Math.min(6.4, Math.sqrt(n.e) * 1.05) : isOP(n) ? 8 : 4.6; };
let curK = 1, litSet = null;
function placeLabels(k = curK, set = litSet){
  curK = k;
  const s = pxPerUnit() * k, fs = (k < 1.4 ? 13 : 12.5) / s, h = fs * 1.2, pad = 3 / s;
  const boxes = [];
  for (const d of nodeData) if (!d.up && (!set || set.has(d.id))){ const r = glyphR(d) + 1.5; boxes.push([d.px - r, d.py - r, d.px + r, d.py + r, d.id]); }
  const hit = (b, self) => boxes.some(c => c[4] !== self && !(b[2] < c[0] || b[0] > c[2] || b[3] < c[1] || b[1] > c[3]));
  const eligible = L => set ? set.has(L.d.id)
    : k < 1.4 ? isWood(L.n) || isOP(L.n)
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
  shootSel.classed("on", e => on(e.t.id) && (!e.s || on(e.s.id)));
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
  if (isWood(n)) return (n.s === "partial" ? "proved in part" : "proved") + (n.e ? ` · ${n.e} corpus ${n.e === 1 ? "entry rests" : "entries rest"} here` : "");
  const bits = [n.op ? "open problem" : "frontier"]; if (n.core?.length) bits.push("core proved"); if (n.st) bits.push(STATUS_TXT[n.st]);
  if (n.seed || n.ground) bits.push("grows from upstream");
  return bits.join(" · ");
}
nodeSel.on("mouseenter", (ev, d) => { if (!selected) light(lineage(d.id)); showTip(ev, `<b>${esc(d.data.node.t)}</b>${esc(statusLine(d.data.node))}`); })
  .on("mousemove", (ev, d) => showTip(ev, `<b>${esc(d.data.node.t)}</b>${esc(statusLine(d.data.node))}`))
  .on("mouseleave", () => { hideTip(); if (!selected) light(null); })
  .on("click", (ev, d) => { ev.stopPropagation(); select(d.id); });
pileSel.on("mouseenter", (ev, p) => { if (!selected) light(new Set(), "pile:" + p.a); showTip(ev, `<b>${p.list.length} ${esc(areaName(p.a))} entries off the map</b>proved, but resting on no node and feeding none`); })
  .on("mousemove", (ev, p) => showTip(ev, `<b>${p.list.length} ${esc(areaName(p.a))} entries off the map</b>proved, but resting on no node and feeding none`))
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
  const kind = isUp(n) ? pill("upstream", "--tr-soil-ink") : isWood(n) ? pill(n.s === "partial" ? "proved in part" : "proved", "--tr-bark") : n.op ? pill("open problem", "--tr-star") : pill("frontier", "--tr-blue");
  const st = n.st ? pill(STATUS_TXT[n.st], STATUS_VAR[n.st]) : "";
  const iss = n.i.slice().sort((a, b) => (a[1] === "o" ? 0 : 1) - (b[1] === "o" ? 0 : 1) || b[0] - a[0]);
  const li = x => `<li><a class="num${x[1] === "o" ? "" : " closed"}" href="${GH}${x[0]}" target="_blank" rel="noopener">#${x[0]}</a><span class="${x[1] === "o" ? "" : "closed"}">${esc(x[3])}${x[2] ? " <span class='muted'>(PR)</span>" : ""}${x[1] === "o" && x[4][0] ? ` <span class="muted">· ${esc(STATUS_TXT[x[4][0]] || x[4][0])}</span>` : ""}${x[1] !== "o" ? " <span class='muted'>· closed</span>" : ""}</span></li>`;
  const uses = n.u.filter(u => N.has(u)), users = n.users;
  return `
    <button class="backbtn" type="button" data-back>← How to read the tree</button>
    <div style="display:flex; gap:6px; flex-wrap:wrap">${kind}${st}<span class="pill">${esc(areaName(n.a))}</span></div>
    <h2>${esc(n.t)}</h2>
    ${n.x ? `<p class="stmt">${prose(n.x)}</p>` : ""}
    ${n.d ? `<div><h3>Lean</h3><div class="mono">${n.h ? `<a href="${esc(n.h)}">${esc(n.d)}</a>` : esc(n.d)}</div>${n.m ? `<div class="muted" style="font-size:12.5px">${esc(n.m)}</div>` : ""}</div>` : ""}
    ${isWood(n) ? `<div><h3>Corpus</h3><p>${n.e ? `<b>${n.e}</b> ${n.e === 1 ? "entry hangs" : "entries hang"} here as leaves: this is the deepest node ${n.e === 1 ? "its proof rests" : "their proofs rest"} on.` : "No entry has this as its deepest node; entries reach it through the nodes above."}</p></div>` : ""}
    ${n.core?.length ? `<div><h3>Core already proved</h3><ul class="entries">${n.core.map(c => `<li><span class="mono">${esc(c)}</span></li>`).join("")}</ul></div>` : ""}
    ${n.sucker && isWood(n) ? `<div><h3>Rests on Mathlib alone</h3><p>No blueprint node is in its proof term, so it grows from the soil beside the trunk rather than from Foundations. If its mathematics does build on a library object, tagging that object or proving the bridge lifts it into the crown.</p></div>` : ""}
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
    <div class="legend">
      <div>${glyph("knot")}<span><b>Wood and knots</b>: proved blueprint nodes; a knot's size counts the corpus entries resting deepest on it. Height is conceptual depth: a node sits above everything it rests on, with Foundations as the trunk. Every use is drawn, and wood thickens with the corpus it carries.</span></div>
      <div>${glyph("leaf")}<span><b>Leaves</b> (the Leaves button): the same corpus entries drawn one by one, hung on the deepest node their proof rests on.</span></div>
      <div>${glyph("bud")}<span><b>Blueprint shoots and buds</b>: frontier nodes. The bud's centre shows the state of its issue.</span></div>
      <div>${glyph("core")}<span><b>Half-filled bud</b>: a frontier node whose core is already proved in the corpus.</span></div>
      <div>${glyph("star")}<span><b>Stars</b>: frontier nodes carried by an open-problem issue.</span></div>
      <div>${glyph("sucker")}<span><b>Stems from the soil</b>: proved nodes outside Foundations that rest on no blueprint node, only on Mathlib. Their build-up on the library is not recorded yet.</span></div>
      <div>${glyph("seed")}<span><b>Seedlings</b>: frontier that grows straight from Mathlib or BrownianMotion, with no proved node beneath it yet.</span></div>
      <div>${glyph("fallen")}<span><b>Fallen leaves</b>: proved entries that rest on no node. Each one is a missing tag or bridge.</span></div>
    </div>
    <div class="chips">${dots()}</div>
    <div><h3>Open problems</h3><div class="chips">${ops.map(n => chip(n.l)).join("")}</div></div>
    <div><h3>Ready to pick up · ${ready.length}</h3><div class="chips">${ready.sort((a, b) => a.t.localeCompare(b.t)).slice(0, 14).map(n => chip(n.l)).join("")}${ready.length > 14 ? ` <span class="muted" style="font-size:12.5px; align-self:center">and ${ready.length - 14} more on the tree</span>` : ""}</div></div>`;
}
function selectPile(a){
  selected = "pile:" + a; light(new Set(), selected); selRing.attr("visibility", "hidden");
  const list = D.off[a] || [];
  folio.innerHTML = `<button class="backbtn" type="button" data-back>← How to read the tree</button>
    <span class="pill"><i style="background:var(--tr-fallen)"></i>off the map</span>
    <h2>${list.length} ${esc(areaName(a))} entries on the ground</h2>
    <p>Proved and imported by the library, but no constant they cite reaches a blueprint node, and no node depends on them. A tag on the object they share, or a bridge to the node they illustrate, lifts them onto the tree.</p>
    <ul class="entries">${list.map(([id, name]) => `<li>${esc(name)}<br><span class="mono">${esc(id)}</span></li>`).join("")}</ul>`;
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

// ---------- leaves on demand ----------
const leavesBtn = document.getElementById("t-leaves");
leavesBtn.onclick = () => { const on = leavesBtn.getAttribute("aria-pressed") !== "true";
  leavesBtn.setAttribute("aria-pressed", on); leafG.attr("display", on ? null : "none"); };

// ---------- growth ----------
const reduce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
const growBtn = document.getElementById("t-grow");
if (reduce) growBtn.hidden = true;
function lvl(d){ return d ? (d.depth ?? 0) : 0; }
growBtn.onclick = () => {
  select(null);
  const step = 260, dur = 420;
  const fade = (sel, delay) => sel.interrupt().style("opacity", 0).transition().delay(delay).duration(dur).style("opacity", null);
  fade(roots.selectAll("path"), 0); fade(view.select(".trunk"), 80);
  fade(branchSel, e => 160 + (e.t.depth + 1) * step); fade(nodeSel.filter(d => d.up || isWood(d.data.node)), d => 220 + (d.depth + 1) * step);
  fade(leafSel, f => 340 + (f.d.depth + 1) * step + f.k * 5);
  const last = 340 + (maxLevel + 1) * step;
  fade(pileSel, last + 150);
  fade(shootSel, e => last + 250 + e.t.depth * 160);
  fade(nodeSel.filter(d => !d.up && !isWood(d.data.node)), d => last + 400 + d.depth * 160);
};

defaultPanel();
placeLabels(1);
})();
