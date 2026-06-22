import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

// ---- coordinate map: lattice (i, j, k=time) -> world (x=i, y=k UP, z=j) ----
const SCENES = [
  { id: 'zmerge',     file: 'scenes/zmerge.json',     name: 'Z-merge  (Z̄₀Z̄₁)' },
  { id: 'xmerge',     file: 'scenes/xmerge.json',     name: 'X-merge  (X̄₀X̄₁)' },
  { id: 'zzz',        file: 'scenes/zzz-merge.json',  name: 'Weight-3 Z-merge  (Z̄₀Z̄₁Z̄₂)' },
  { id: 'routed',     file: 'scenes/routed.json',     name: 'Routed long-range merge {0,3}' },
  { id: 'cnot',       file: 'scenes/cnot.json',       name: 'CNOT  (LaSsynth multi-merge)' },
  { id: 'cz',         file: 'scenes/cz.json',         name: 'CZ  (mixed-basis, LaSsynth)' },
  { id: 'hadamard',   file: 'scenes/hadamard.json',   name: 'Hadamard  (patch rotation, yellow)' },
  { id: 'majority',   file: 'scenes/majority.json',   name: 'Majority / CCZ junction  (9 flows)' },
  { id: 'crosslayer', file: 'scenes/crosslayer.json', name: 'Cross-layer  Z-merge ; Ȳ-readout' },
];
const COL = { blue: 0x3b82f6, red: 0xef4444, green: 0x22c55e, patch: 0xb9c2cf, corner: 0x9aa4af };
const FLOWCOL = [0x60a5fa, 0xf472b6, 0xfbbf24, 0x34d399, 0xa78bfa, 0xf87171, 0x22d3ee, 0xfb923c];

const app = document.getElementById('app');
const tip = document.getElementById('tip');
const scene = new THREE.Scene();
scene.background = new THREE.Color(0x0e1116);

const camera = new THREE.PerspectiveCamera(45, innerWidth/innerHeight, 0.1, 500);
const renderer = new THREE.WebGLRenderer({ antialias:true });
renderer.setPixelRatio(devicePixelRatio); renderer.setSize(innerWidth, innerHeight);
renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
app.appendChild(renderer.domElement);

const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true; controls.dampingFactor = 0.08;

// ---- lights (soft SketchUp-ish) ----
scene.add(new THREE.HemisphereLight(0xffffff, 0x2a2f37, 0.55));
const key = new THREE.DirectionalLight(0xffffff, 1.1);
key.position.set(6, 12, 8); key.castShadow = true;
key.shadow.mapSize.set(2048,2048); key.shadow.camera.near=1; key.shadow.camera.far=80;
key.shadow.camera.left=-20; key.shadow.camera.right=20; key.shadow.camera.top=20; key.shadow.camera.bottom=-20;
scene.add(key);
const fill = new THREE.DirectionalLight(0x9bb8ff, 0.35); fill.position.set(-8,5,-6); scene.add(fill);

const root = new THREE.Group(); scene.add(root);
const ground = new THREE.Mesh(new THREE.PlaneGeometry(200,200),
  new THREE.MeshStandardMaterial({ color:0x12161c, roughness:1 }));
ground.rotation.x = -Math.PI/2; ground.position.y = -0.02; ground.receiveShadow = true; scene.add(ground);

// ---- materials ----
// A surface-code patch has a SMOOTH (Z, blue) boundary pair and a ROUGH (X, red)
// pair; `blueAxis` (per scene) says which spatial axis carries the smooth one.
const matTime = new THREE.MeshStandardMaterial({ color:0xc7d0db, roughness:0.6, metalness:0.04 });
const matY    = new THREE.MeshStandardMaterial({ color:COL.green, roughness:0.4, emissive:0x0b3b1e });
function faceMat(hex){ return new THREE.MeshStandardMaterial({ color:hex, roughness:0.5, metalness:0.06 }); }
function surfMat(color){ return new THREE.MeshStandardMaterial({ color, transparent:true, opacity:0.34,
  side:THREE.DoubleSide, depthWrite:false, roughness:0.3, emissive:color, emissiveIntensity:0.18 }); }
// BoxGeometry group order [+x,-x,+y,-y,+z,-z] = [+i,-i,+k(time),-k(time),+j,-j].
// A WORLDLINE extends in time, so its time-faces (±k) are caps = grey, exposed ONLY
// at a port. A MERGE seam extends in SPACE, so its time-faces are NOT caps — they
// take the merge's boundary colour (never grey; grey is a port-only thing).
// `bi` = is the I-axis the smooth (blue, Z) boundary at this point? A Hadamard
// SWAPS it, so the colour is a function of time (basisAt) — blue/red interleave
// across the yellow rotation, which is the whole point of an H.
function patchFaceMats(bi){
  const iC = bi ? COL.blue : COL.red;   // ±i boundary faces
  const jC = bi ? COL.red  : COL.blue;  // ±j boundary faces
  return [faceMat(iC), faceMat(iC), matTime.clone(), matTime.clone(), faceMat(jC), faceMat(jC)];
}
// Merge-seam / merge-junction faces: time-faces (±k) take the merge-direction colour
// (the bridge is spatial, not a temporal cap), so a merge bridge is NEVER grey.
function seamFaceMatsI(bi){   // I-pipe (along i): ±i & ±k = i-colour (merge dir), ±j sides = j-colour
  const iC = bi ? COL.blue : COL.red, jC = bi ? COL.red : COL.blue;
  return [faceMat(iC),faceMat(iC), faceMat(iC),faceMat(iC), faceMat(jC),faceMat(jC)]; }
function seamFaceMatsJ(bi){   // J-pipe (along j): ±j & ±k = j-colour (merge dir), ±i sides = i-colour
  const iC = bi ? COL.blue : COL.red, jC = bi ? COL.red : COL.blue;
  return [faceMat(iC),faceMat(iC), faceMat(jC),faceMat(jC), faceMat(jC),faceMat(jC)]; }
// The boundary basis at time-level k: a rotation (ROT) flips it from inBi (below the
// rotation node) to outBi (above); without a rotation it is the global BAxisI.
function basisAt(k){ return ROT ? (k < ROT.k ? ROT.inBi : ROT.outBi) : BAxisI; }

const pickable = [];
let surfaceGroup = new THREE.Group(); root.add(surfaceGroup);
let usePerFlow = false, showSurf = false, BAxisI = true, ROT = null;   // backbone-only; ROT = active rotation

function clearRoot(){
  for (const o of [...root.children]) { if (o!==surfaceGroup) root.remove(o); }
  surfaceGroup.clear(); pickable.length = 0;
}
function addMesh(mesh, label){ mesh.userData.label = label; mesh.castShadow = true; mesh.receiveShadow = true;
  pickable.push(mesh); return mesh; }

const W = 0.46;          // pipe cross-section
// Fresh materials per mesh so the hover highlight (which boosts emissive) stays local.
// Worldlines are K-pipes (node→node in time); seams are I/J-pipes spanning the GAP
// between two nodes (length 1-W) so they butt flush against the patch/cube at each
// end. Junction (node) cubes fill any node that has no worldline — e.g. ancilla-
// highway nodes — so corners are solid instead of gapping.
function worldline(i,j,k,label){
  const m = new THREE.Mesh(new THREE.BoxGeometry(W,1.0,W), patchFaceMats(basisAt(k)));
  m.position.set(i, k+0.5, j); root.add(addMesh(m,label)); }
function nodeCube(i,j,k,axis,label){   // a merge junction → merge colouring (no grey caps)
  const mats = axis==='J' ? seamFaceMatsJ(basisAt(k)) : seamFaceMatsI(basisAt(k));
  const m = new THREE.Mesh(new THREE.BoxGeometry(W,W,W), mats);
  m.position.set(i, k, j); root.add(addMesh(m,label)); }
// A merge seam is a PATCH EXTENSION, not a special element: a Z-merge extends the Z
// boundary along i while its two X (red) side boundaries run alongside. Its time-faces
// take the merge colour (seamFaceMats), so the bridge is never grey and never a single
// flat colour — grey is reserved for worldline port caps only.
function zseam(i,j,k,color,label){   // I-pipe weld, gap between node (i,j,k) and (i+1,j,k)
  const m = new THREE.Mesh(new THREE.BoxGeometry(1-W,W,W), seamFaceMatsI(basisAt(k)));
  m.position.set(i+0.5, k, j); root.add(addMesh(m,label)); }
function xseam(i,j,k,color,label){   // J-pipe weld, gap between node (i,j,k) and (i,j+1,k)
  const m = new THREE.Mesh(new THREE.BoxGeometry(W,W,1-W), seamFaceMatsJ(basisAt(k)));
  m.position.set(i, k, j+0.5); root.add(addMesh(m,label)); }
function ycube(i,j,k,label){
  const m = new THREE.Mesh(new THREE.OctahedronGeometry(0.4), matY.clone());
  m.position.set(i, k+0.5, j); root.add(addMesh(m,label)); }
// A color ROTATION (Hadamard / patch rotation) — a short YELLOW tube segment
// injected into the worldline where the smooth/rough boundary swaps (X̄↔Z̄), so
// the boundary colours legitimately interleave across it.
function rotation(i,j,k,label){
  const m = new THREE.Mesh(new THREE.BoxGeometry(W*1.08,0.16,W*1.08),   // SHORT band at the swap
    new THREE.MeshStandardMaterial({ color:0xeab308, emissive:0x6b5300, emissiveIntensity:0.5, roughness:0.4 }));
  m.position.set(i, k, j); root.add(addMesh(m,label)); }
// A port = the qubit's input/output boundary, marked by a small GREEN CUBE hat:
// the SAME W×W cross-section as the pipe, very short, sitting flush on the pipe end
// (which also caps the worldline's grey time-face). dir = above for an output port
// (top), below for an input port (bottom).
const PH = 0.2;   // port-hat height (short)
function port(i,j,k,top,label){
  const dir = top ? 1 : -1;
  const hat = new THREE.Mesh(new THREE.BoxGeometry(W, PH, W),
    new THREE.MeshStandardMaterial({ color:COL.green, emissive:0x0b3b1e, emissiveIntensity:0.3, roughness:0.45 }));
  hat.position.set(i, k + dir*(PH/2), j);
  root.add(addMesh(hat, label + ' — green port hat (init/measure boundary)')); }

// Detect a Hadamard / patch rotation: a column whose ports carry BOTH z-bases
// (blueSel 4=KI and 5=KJ). Returns the swap node k (midpoint) and the basis below
// (inBi) and above (outBi) it — blueSel 4 ⇒ I-axis smooth (bi=true), 5 ⇒ J (false).
function detectRotation(sc){
  const byCol = {};
  for (const p of (sc.ports||[])) (byCol[p.i+','+p.j] ||= []).push(p);
  for (const key in byCol){
    const ps = byCol[key];
    if (ps.some(p=>p.blueSel===4) && ps.some(p=>p.blueSel===5)){
      const lo = ps.reduce((a,b)=>b.k<a.k?b:a), hi = ps.reduce((a,b)=>b.k>a.k?b:a);
      return { k: Math.round((lo.k+hi.k)/2), inBi: lo.blueSel===4, outBi: hi.blueSel===4 };
    }
  }
  return null;
}

// correlation-surface cell: a translucent colored quad, oriented by plane
function surfQuad(cell){
  const c = usePerFlow ? FLOWCOL[cell.flow % FLOWCOL.length]
            : (cell.color==='blue'?COL.blue : cell.color==='red'?COL.red : COL.corner);
  const g = new THREE.PlaneGeometry(0.92, 0.92);
  const m = new THREE.Mesh(g, surfMat(c));
  const i=cell.i, j=cell.j, k=cell.k;
  switch(cell.plane){
    case 'KI': m.position.set(i, k+0.5, j); break;                                  // Z̄ sheet on worldline (faces +z)
    case 'KJ': m.position.set(i, k+0.5, j); m.rotation.y = Math.PI/2; break;         // X̄ sheet (faces +x)
    case 'IK': m.position.set(i+0.5, k, j); m.rotation.x = -Math.PI/2; break;        // joint-Z bridge at seam
    case 'JK': m.position.set(i, k, j+0.5); m.rotation.z =  Math.PI/2; m.rotation.x=-Math.PI/2; break;
    default:   m.position.set(i, k+0.5, j); m.rotation.x = -Math.PI/2;               // corner pieces
  }
  m.userData.label = cell.label; surfaceGroup.add(m); pickable.push(m);
}

function frameCamera(d){
  const cx=(d.maxI-1)/2, cy=(d.maxK-1)/2, cz=(d.maxJ-1)/2;
  controls.target.set(cx, cy, cz);
  const r = Math.max(d.maxI, d.maxJ, d.maxK) + 3;
  camera.position.set(cx + r*1.1, cy + r*0.9, cz + r*1.3);
  camera.near = 0.1; camera.far = 500; camera.updateProjectionMatrix();
  controls.update();
}

let current = null;
async function load(file){
  const sc = await (await fetch(file)).json();
  current = sc; BAxisI = (sc.blueAxis !== 'J'); ROT = detectRotation(sc); clearRoot();
  for (const c of sc.cubes){
    if (c.kind==='worldline') worldline(c.i,c.j,c.k,c.label);
    else if (c.kind==='zseam') zseam(c.i,c.j,c.k,c.color,c.label);
    else if (c.kind==='xseam') xseam(c.i,c.j,c.k,c.color,c.label);
    else if (c.kind==='ycube') ycube(c.i,c.j,c.k,c.label);
    else if (c.kind==='rotation') rotation(c.i,c.j,c.k,c.label);
  }
  // junction (node) cubes at EVERY merge-seam endpoint — fills the corner where a
  // weld meets a patch (the CNOT hollow) AND gives ancilla-highway nodes their patch.
  // Same two-tone material as the patches, so any overlap with a worldline is the
  // same colour (invisible) and corners read solid instead of exposing a grey cap.
  const need = new Map();
  for (const c of sc.cubes){
    if (c.kind==='zseam'){ need.set(`${c.i},${c.j},${c.k}`,[c.i,c.j,c.k,'I']); need.set(`${c.i+1},${c.j},${c.k}`,[c.i+1,c.j,c.k,'I']); }
    else if (c.kind==='xseam'){ need.set(`${c.i},${c.j},${c.k}`,[c.i,c.j,c.k,'J']); need.set(`${c.i},${c.j+1},${c.k}`,[c.i,c.j+1,c.k,'J']); }
  }
  for (const [,[i,j,k,axis]] of need) nodeCube(i,j,k,axis, `patch node (${i},${j}) @ t=${k} (merge junction)`);
  for (const s of sc.surfaces) surfQuad(s);
  for (const p of sc.ports){
    port(p.i,p.j,p.k, p.k >= sc.dims.maxK-1, p.label);
  }
  surfaceGroup.visible = showSurf;
  frameCamera(sc.dims);
  document.getElementById('meta').textContent =
    `${sc.name} · ${sc.dims.maxI}×${sc.dims.maxJ}×${sc.dims.maxK} grid · ${sc.nStab} flows · ` +
    `smooth(Z,blue) boundary on ${sc.blueAxis}-axis · ${sc.cubes.length} pieces`;
  refresh2d();
}

// ---- hover tooltip + highlight (handles single OR multi-material meshes) ----
const ray = new THREE.Raycaster(); const ndc = new THREE.Vector2(); let hovered=null;
function eachMat(mesh, fn){ const m=mesh.material; Array.isArray(m) ? m.forEach(fn) : fn(m); }
function unhover(){ if(!hovered) return;
  eachMat(hovered, m=>{ if(m.userData.__e!==undefined){ m.emissive.setHex(m.userData.__e);
    m.emissiveIntensity=m.userData.__ei; m.userData.__e=undefined; } });
  hovered=null; }
addEventListener('pointermove', (e)=>{
  ndc.x = (e.clientX/innerWidth)*2-1; ndc.y = -(e.clientY/innerHeight)*2+1;
  ray.setFromCamera(ndc, camera);
  const hit = ray.intersectObjects(pickable, false)[0];
  if (hit){
    const o = hit.object;
    if (hovered!==o){ unhover(); hovered=o;
      eachMat(o, m=>{ m.userData.__e=m.emissive.getHex(); m.userData.__ei=m.emissiveIntensity;
        m.emissive.setHex(0xffffff); m.emissiveIntensity=0.4; }); }
    tip.style.display='block'; tip.textContent = o.userData.label;
    tip.style.left = Math.min(e.clientX+14, innerWidth-360)+'px';
    tip.style.top = (e.clientY+12)+'px';
  } else { unhover(); tip.style.display='none'; }
});

// ---- UI ----
const sel = document.getElementById('scene');
for (const s of SCENES){ const o=document.createElement('option'); o.value=s.file; o.textContent=s.name; sel.appendChild(o); }
sel.onchange = ()=> load(sel.value);
document.getElementById('reset').onclick = ()=> current && frameCamera(current.dims);
document.getElementById('tSurf').onchange = (e)=>{ showSurf=e.target.checked; surfaceGroup.visible=showSurf; };
document.getElementById('tFlows').onchange = (e)=>{ usePerFlow=e.target.checked; if(current) load(sel.value); };

// ============================================================================
//  2D flattened animation — top-down (i,j) view, stepped through time k.
//  Shows exactly how each merge/split happens, slice by slice.
// ============================================================================
const app2d = document.getElementById('app2d');
const cvs = document.getElementById('c2d'); const ctx = cvs.getContext('2d');
const tk = document.getElementById('tk'); const tlab = document.getElementById('tlab');
let mode = '3d', frame = 0, playing = false, playTimer = null;

function presentPatches(){ // union of all worldline (i,j) over time → stable layout
  const s = new Map();
  for (const c of current.cubes) if (c.kind==='worldline') s.set(c.i+','+c.j, [c.i,c.j]);
  return [...s.values()];
}
function setMode(m){
  mode = m;
  document.getElementById('m3d').classList.toggle('on', m==='3d');
  document.getElementById('m2d').classList.toggle('on', m==='2d');
  app.style.display      = m==='3d' ? 'block':'none';
  app2d.style.display    = m==='2d' ? 'block':'none';
  document.getElementById('play').style.display = m==='2d' ? 'flex':'none';
  document.getElementById('hint').textContent = m==='2d'
    ? 'play ▶ to watch each merge / split · drag the slider to scrub time'
    : 'drag to rotate · scroll to zoom · right-drag to pan · hover a piece for its meaning';
  if (m==='2d'){ stopPlay(); resize2d(); draw2d(frame); }
}
function refresh2d(){
  if (!current) return;
  const maxFrame = Math.max(0, current.dims.maxK-1);
  tk.max = maxFrame; if (frame>maxFrame) frame = 0; tk.value = frame;
  if (mode==='2d') draw2d(frame);
}
function resize2d(){
  const dpr = devicePixelRatio||1;
  cvs.width = innerWidth*dpr; cvs.height = innerHeight*dpr;
  ctx.setTransform(dpr,0,0,dpr,0,0);
}
function layout(){
  const d = current.dims, pad = 90;
  const pitchX = (innerWidth -2*pad)/Math.max(1,d.maxI);
  const pitchY = (innerHeight-2*pad-40)/Math.max(1,d.maxJ);
  const pitch  = Math.min(150, pitchX, pitchY);
  const cell   = pitch*0.66;
  const ox = (innerWidth  - pitch*(d.maxI-1))/2 - cell/2;
  const oy = (innerHeight - pitch*(d.maxJ-1))/2 - cell/2 + 10;
  return { pitch, cell, ox, oy,
    cx:(i)=>ox+i*pitch, cy:(j)=>oy+j*pitch };
}
function rrect(x,y,w,h,r){ ctx.beginPath(); ctx.roundRect(x,y,w,h,r); }
function draw2d(k){
  if (!current) return;
  const L = layout(), C = L.cell;
  ctx.clearRect(0,0,innerWidth,innerHeight);
  const at = (arr,kind)=>arr.filter(c=>c.k===k && (kind?c.kind===kind:true));
  const here = new Set(at(current.cubes,'worldline').map(c=>c.i+','+c.j));
  // ancilla highway nodes: seam endpoints with no worldline this slice → draw as patches
  for (const s of at(current.cubes,'zseam')){ here.add(`${s.i},${s.j}`); here.add(`${s.i+1},${s.j}`); }
  for (const s of at(current.cubes,'xseam')){ here.add(`${s.i},${s.j}`); here.add(`${s.i},${s.j+1}`); }
  const surfHere = current.surfaces.filter(s=>s.k===k);

  // 1) ghost layout (every patch that ever exists)
  for (const [i,j] of presentPatches()){
    rrect(L.cx(i),L.cy(j),C,C,10);
    ctx.strokeStyle='#2b3138'; ctx.lineWidth=1.5; ctx.setLineDash([5,5]); ctx.stroke(); ctx.setLineDash([]);
  }
  const bi = basisAt(k);                       // per-slice basis (swaps across a rotation)
  const iC = bi ? '#3b82f6' : '#ef4444';       // ±i (left/right) boundary
  const jC = bi ? '#ef4444' : '#3b82f6';       // ±j (top/bottom) boundary
  const grad=(x,y,h)=>{ const g=ctx.createLinearGradient(x,y,x,y+h); g.addColorStop(0,'#cfd8e3'); g.addColorStop(1,'#aab4c2'); return g; };
  // 2) merges = patch EXTENSION: fill the gap with patch material; the boundary
  //    running ALONG the merge keeps its colour (continuous across the weld).
  for (const s of at(current.cubes,'zseam')){            // I-merge along i → j-boundary (top/bottom) continues
    const x=L.cx(s.i)+C, y=L.cy(s.j), w=L.pitch-C;
    ctx.fillStyle=grad(x,y,C); rrect(x,y,w,C,2); ctx.fill();
    ctx.lineWidth=4; ctx.lineCap='round'; ctx.strokeStyle=jC;
    ctx.beginPath(); ctx.moveTo(x,y); ctx.lineTo(x+w,y); ctx.moveTo(x,y+C); ctx.lineTo(x+w,y+C); ctx.stroke();
  }
  for (const s of at(current.cubes,'xseam')){            // J-merge along j → i-boundary (left/right) continues
    const x=L.cx(s.i), y=L.cy(s.j)+C, h=L.pitch-C;
    ctx.fillStyle=grad(x,y,h); rrect(x,y,C,h,2); ctx.fill();
    ctx.lineWidth=4; ctx.lineCap='round'; ctx.strokeStyle=iC;
    ctx.beginPath(); ctx.moveTo(x,y); ctx.lineTo(x,y+h); ctx.moveTo(x+C,y); ctx.lineTo(x+C,y+h); ctx.stroke();
  }
  // 3) present patches — two-tone boundary edges (smooth Z blue / rough X red)
  for (const key of here){
    const [i,j]=key.split(',').map(Number);
    const X=L.cx(i), Y=L.cy(j);
    rrect(X,Y,C,C,8);
    const g = ctx.createLinearGradient(X,Y,X,Y+C);
    g.addColorStop(0,'#cfd8e3'); g.addColorStop(1,'#aab4c2'); ctx.fillStyle=g; ctx.fill();
    ctx.lineWidth=4; ctx.lineCap='round';
    ctx.strokeStyle=iC; ctx.beginPath(); ctx.moveTo(X,Y); ctx.lineTo(X,Y+C); ctx.moveTo(X+C,Y); ctx.lineTo(X+C,Y+C); ctx.stroke();
    ctx.strokeStyle=jC; ctx.beginPath(); ctx.moveTo(X,Y); ctx.lineTo(X+C,Y); ctx.moveTo(X,Y+C); ctx.lineTo(X+C,Y+C); ctx.stroke();
    ctx.fillStyle='#0d1117'; ctx.font='12px ui-monospace,monospace'; ctx.textAlign='center';
    ctx.fillText(`${i},${j}`, X+C/2, Y+C/2+4);
  }
  // 4) Y-cubes (green diamond)
  for (const c of at(current.cubes,'ycube')){
    const x=L.cx(c.i)+C/2, y=L.cy(c.j)+C/2;
    ctx.save(); ctx.translate(x,y); ctx.rotate(Math.PI/4);
    ctx.fillStyle='#22c55e'; rrect(-C*0.22,-C*0.22,C*0.44,C*0.44,4); ctx.fill(); ctx.restore();
  }
  // 4b) color rotation (Hadamard) — yellow ring on the patch
  for (const c of at(current.cubes,'rotation')){
    const x=L.cx(c.i)+C/2, y=L.cy(c.j)+C/2;
    ctx.strokeStyle='#eab308'; ctx.lineWidth=5; ctx.beginPath(); ctx.arc(x,y,C*0.3,0,Math.PI*2); ctx.stroke();
  }
  // 5) caption
  const merging = at(current.cubes,'zseam').length+at(current.cubes,'xseam').length>0;
  const ys = at(current.cubes,'ycube').length>0;
  const what = ys ? 'Ȳ init / measure' : merging ? 'MERGE — joint stabilizer measurement' : 'idle (patches stored)';
  ctx.fillStyle='#e6edf3'; ctx.font='600 16px -apple-system,Segoe UI,sans-serif'; ctx.textAlign='left';
  ctx.fillText(`${current.name}`, 24, 34);
  ctx.fillStyle='#8b949e'; ctx.font='13px -apple-system,Segoe UI,sans-serif';
  ctx.fillText(`time slice  t = ${k} / ${current.dims.maxK-1}`, 24, 56);
  tlab.textContent = `t = ${k} · ${what}`;
}
function stopPlay(){ playing=false; document.getElementById('pPlay').textContent='▶';
  if (playTimer){ clearInterval(playTimer); playTimer=null; } }
function startPlay(){ if(!current) return; playing=true; document.getElementById('pPlay').textContent='⏸';
  playTimer = setInterval(()=>{
    const max=Number(tk.max); frame = frame>=max ? 0 : frame+1; tk.value=frame; draw2d(frame);
  }, 850); }
document.getElementById('m3d').onclick = ()=> setMode('3d');
document.getElementById('m2d').onclick = ()=> setMode('2d');
document.getElementById('pPlay').onclick = ()=> playing ? stopPlay() : startPlay();
document.getElementById('pStep').onclick = ()=>{ stopPlay(); frame=Math.max(0,frame-1); tk.value=frame; draw2d(frame); };
document.getElementById('pNext').onclick = ()=>{ stopPlay(); frame=Math.min(Number(tk.max),frame+1); tk.value=frame; draw2d(frame); };
tk.oninput = ()=>{ stopPlay(); frame=Number(tk.value); draw2d(frame); };

addEventListener('resize', ()=>{ camera.aspect=innerWidth/innerHeight; camera.updateProjectionMatrix();
  renderer.setSize(innerWidth, innerHeight); if(mode==='2d'){ resize2d(); draw2d(frame); } });
(function animate(){ requestAnimationFrame(animate); controls.update();
  if(mode==='3d') renderer.render(scene,camera); })();

load(SCENES[0].file);
