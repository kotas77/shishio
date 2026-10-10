// ふたりの将棋盤 — 自由に動かせる将棋盤（本将棋・王手将棋・獅子対応）
(function(){
const NAMES={K:"玉",R:"飛",B:"角",G:"金",S:"銀",N:"桂",L:"香",P:"歩",X:"獅","+R":"龍","+B":"馬","+S":"全","+N":"圭","+L":"杏","+P":"と"};
const PROMOTABLE="RBSNLP";
const HAND_ORDER=["R","B","G","S","N","L","P","X"];
const PALETTE=["K","R","B","G","S","N","L","P","X"];
const ZEN="０１２３４５６７８９", KAN=["一","二","三","四","五","六","七","八","九"];
const CLIENT=Math.random().toString(36).slice(2);
const HIST_MAX=150;
const RULE_HELP={
  hon:"玉を取った側の勝ちと判定し、王手がかかると知らせます。詰みや反則の自動判定はしません。",
  oute:"先に王手をかけた側の勝ちです。指した直後に相手の玉へ利きがあれば、その時点で決着します。",
  free:"勝敗の判定をしません。獅子入りなど独自ルールの対局や検討に使えます。"
};

function initialBoard(){
  const r=s=>s.split(",");
  return [].concat(
    r("l,n,s,g,k,g,s,n,l"), r(",r,,,,,,b,"), Array(9).fill("p"),
    Array(27).fill(""),
    Array(9).fill("P"), r(",B,,,,,,R,"), r("L,N,S,G,K,G,S,N,L"));
}
function initial(){
  return {board:initialBoard(), hands:{b:{},w:{}}, moves:[], last:null, hist:[], rev:0, by:"", variant:"hon", result:null};
}
const owner=p=>{const c=p.replace("+","");return c===c.toUpperCase()?"b":"w"};
const base=p=>p.replace("+","").toUpperCase();
const isPro=p=>p.startsWith("+");
const label=p=>{const k=isPro(p)?"+"+base(p):base(p); if(k==="K") return owner(p)==="b"?"玉":"王"; return NAMES[k]};
const coord=i=>ZEN[9-(i%9)]+KAN[Math.floor(i/9)];
const inZone=(o,i)=>{const r=Math.floor(i/9);return o==="b"?r<=2:r>=6};
const clone=s=>JSON.parse(JSON.stringify(s));
const sideName=o=>o==="b"?"☗ 先手":"☖ 後手";
const asOwner=(k,o)=>o==="b"?k:k.toLowerCase();

/* ---------- 駒の利き（先手から見た向き。後手は上下反転） ---------- */
const K8=[[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]];
const GOLD=[[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,0]];
const ORTH=[[-1,0],[1,0],[0,-1],[0,1]], DIAG=[[-1,-1],[-1,1],[1,-1],[1,1]];
const LION=(()=>{const a=[];for(let r=-2;r<=2;r++)for(let c=-2;c<=2;c++)if(r||c)a.push([r,c]);return a})();
function movesOf(p){
  const k=isPro(p)?"+"+base(p):base(p);
  switch(k){
    case "K": return {st:K8,sl:[]};
    case "G": case "+S": case "+N": case "+L": case "+P": return {st:GOLD,sl:[]};
    case "S": return {st:[[-1,-1],[-1,0],[-1,1],[1,-1],[1,1]],sl:[]};
    case "N": return {st:[[-2,-1],[-2,1]],sl:[]};
    case "P": return {st:[[-1,0]],sl:[]};
    case "L": return {st:[],sl:[[-1,0]]};
    case "R": return {st:[],sl:ORTH};
    case "B": return {st:[],sl:DIAG};
    case "+R": return {st:DIAG,sl:ORTH};
    case "+B": return {st:ORTH,sl:DIAG};
    case "X": return {st:LION,sl:[]};   // 獅子：玉の動きを2回できるので、2マス以内すべてに利く
  }
  return {st:[],sl:[]};
}
function attacks(board,i,t){
  const p=board[i], f=owner(p)==="b"?1:-1;
  const r0=Math.floor(i/9), c0=i%9, tr=Math.floor(t/9), tc=t%9, m=movesOf(p);
  for(const [dr,dc] of m.st){ if(r0+dr*f===tr&&c0+dc*f===tc) return true; }
  for(const [dr,dc] of m.sl){
    let r=r0+dr*f, c=c0+dc*f;
    while(r>=0&&r<9&&c>=0&&c<9){
      if(r===tr&&c===tc) return true;
      if(board[r*9+c]) break;
      r+=dr*f; c+=dc*f;
    }
  }
  return false;
}
function checkedKings(board,def){
  const out=[];
  for(let t=0;t<81;t++){
    const p=board[t]; if(!p||base(p)!=="K"||owner(p)!==def) continue;
    for(let i=0;i<81;i++){ const q=board[i]; if(q&&owner(q)!==def&&attacks(board,i,t)){ out.push(t); break; } }
  }
  return out;
}
function judge(ns,mover,cap){
  ns.result=null;
  if(ns.variant==="free") return;
  const opp=mover==="b"?"w":"b";
  if(cap&&base(cap)==="K"){ ns.result={w:mover,t:sideName(mover)+"の勝ち（玉を取りました）"}; return; }
  if(ns.variant==="oute"&&checkedKings(ns.board,opp).length){ ns.result={w:mover,t:sideName(mover)+"の勝ち（王手）"}; }
}

let S=initial();
let sel=null;            // {type:"board",idx} | {type:"hand",owner,piece} | {type:"pal",piece}
let promo=null;          // {to, moveIdx, piece}
let lionStep=null;       // 獅子の1歩目の後 {at, from, moveIdx}
const cheb=(a,b)=>Math.max(Math.abs(Math.floor(a/9)-Math.floor(b/9)),Math.abs(a%9-b%9));
let editing=false;
let side="b";
try{ if(localStorage.getItem("shogi-side")==="w") side="w"; }catch(e){}
let readOnly=false, writing=false, dirty=false, pendingRemote=null;

const $=id=>document.getElementById(id);

function snapshotOf(s,withMoves){
  const o={b:s.board.join(","),h:s.hands,m:s.moves.length,l:s.last,r:s.result||null};
  if(withMoves) o.mv=s.moves;
  return JSON.stringify(o);
}
function next(withMoves){
  const ns=clone(S);
  ns.hist.push(snapshotOf(S,withMoves));
  if(ns.hist.length>HIST_MAX) ns.hist.splice(0,ns.hist.length-HIST_MAX);
  return ns;
}
function commit(ns){
  ns.rev=(S.rev||0)+1; ns.by=CLIENT;
  S=ns; render(); flush();
}

/* ---------- 対局の操作 ---------- */
function doMove(from,to){
  const ns=next(); const pc=ns.board[from], cap=ns.board[to], o=owner(pc);
  if(cap){ const k=base(cap); ns.hands[o][k]=(ns.hands[o][k]||0)+1; }
  ns.board[to]=pc; ns.board[from]="";
  const prev=S.moves[S.moves.length-1];
  ns.moves.push({n:(o==="b"?"▲":"△")+(prev&&prev.to===to?"同":coord(to))+label(pc), to});
  ns.last={from,to};
  sel=null;
  judge(ns,o,cap);
  promo=(!ns.result&&!isPro(pc)&&PROMOTABLE.includes(base(pc))&&(inZone(o,from)||inZone(o,to)))?{to,moveIdx:ns.moves.length-1,piece:pc}:null;
  commit(ns);
}
/* 獅子：1歩目（取ってもよい）→ 2歩目（元のマスへ戻るのも可）／止める */
function lionFirst(from,to){
  const ns=next(); const pc=ns.board[from], cap=ns.board[to], o=owner(pc);
  if(cap){ const k=base(cap); ns.hands[o][k]=(ns.hands[o][k]||0)+1; }
  ns.board[to]=pc; ns.board[from]="";
  const prev=S.moves[S.moves.length-1];
  ns.moves.push({n:(o==="b"?"▲":"△")+(prev&&prev.to===to?"同":coord(to))+label(pc), to});
  ns.last={from,to};
  promo=null;
  judge(ns,o,cap);
  lionStep=ns.result?null:{at:to,from,moveIdx:ns.moves.length-1};
  sel=lionStep?{type:"board",idx:to}:null;
  commit(ns);
}
function lionSecond(to){
  const {at,from,moveIdx}=lionStep;
  const ns=next(); const pc=ns.board[at], cap=ns.board[to], o=owner(pc);
  if(cap){ const k=base(cap); ns.hands[o][k]=(ns.hands[o][k]||0)+1; }
  ns.board[to]=pc; ns.board[at]="";
  if(ns.moves[moveIdx]){ ns.moves[moveIdx].n+="→"+coord(to)+(to===from?"（戻る）":""); ns.moves[moveIdx].to=to; }
  ns.last={from,to};
  lionStep=null; sel=null;
  judge(ns,o,cap);
  commit(ns);
}
function lionStop(){ lionStep=null; sel=null; render(); }

function doDrop(o,k,to){
  const ns=next();
  ns.hands[o][k]--; if(!ns.hands[o][k]) delete ns.hands[o][k];
  ns.board[to]=asOwner(k,o);
  ns.moves.push({n:(o==="b"?"▲":"△")+coord(to)+label(ns.board[to])+"打", to});
  ns.last={from:null,to};
  sel=null; promo=null;
  judge(ns,o,null);
  commit(ns);
}
function toHand(o,idx){
  const ns=next(); const k=base(ns.board[idx]);
  if(k==="K"){ sel=null; render(); return; }
  ns.hands[o][k]=(ns.hands[o][k]||0)+1; ns.board[idx]="";
  sel=null; promo=null; commit(ns);
}
function togglePromote(idx){
  const p=S.board[idx]; if(!p) return;
  if(!isPro(p)&&!PROMOTABLE.includes(base(p))) return;
  const ns=next(); ns.board[idx]=isPro(p)?p.slice(1):"+"+p;
  if(!editing) judge(ns,owner(p),null);
  commit(ns);
}
function answerPromo(yes){
  if(!promo) return;
  const {to,moveIdx,piece}=promo; promo=null;
  if(S.board[to]!==piece||!S.moves[moveIdx]){ render(); return; }
  const ns=clone(S);
  if(yes){ ns.board[to]="+"+piece; ns.moves[moveIdx].n+="成"; judge(ns,owner(piece),null); }
  else ns.moves[moveIdx].n+="不成";
  commit(ns);
}
function undo(){
  if(!S.hist.length) return;
  const ns=clone(S); const snap=JSON.parse(ns.hist.pop());
  ns.board=snap.b.split(","); ns.hands=snap.h; ns.last=snap.l; ns.result=snap.r||null;
  ns.moves=snap.mv?snap.mv:ns.moves.slice(0,snap.m);
  sel=null; promo=null; lionStep=null; commit(ns);
}
function newGame(){
  const ns=next(true);
  ns.board=initialBoard(); ns.hands={b:{},w:{}}; ns.moves=[]; ns.last=null; ns.result=null;
  sel=null; promo=null; lionStep=null; commit(ns);
}
function setVariant(v){
  if(S.variant===v) return;
  const ns=next(); ns.variant=v; ns.result=null;
  commit(ns);
}

/* ---------- 配置編集 ---------- */
function editPlace(a,piece){
  const ns=next();
  ns.board[a]=ns.board[a]===piece?"":piece; ns.last=null;
  commit(ns);
}
function editMove(from,to){
  const ns=next(); ns.board[to]=ns.board[from]; ns.board[from]=""; ns.last=null;
  sel=null; commit(ns);
}
function editHandAdd(o,k){
  if(k==="K") return;
  const ns=next(); ns.hands[o][k]=(ns.hands[o][k]||0)+1; commit(ns);
}
function editHandRemove(o,k){
  const ns=next(); ns.hands[o][k]--; if(!ns.hands[o][k]) delete ns.hands[o][k]; commit(ns);
}
function editFlipOwner(idx){
  const p=S.board[idx]; if(!p) return;
  const ns=next(); const k=p.replace("+",""); const flipped=k===k.toUpperCase()?k.toLowerCase():k.toUpperCase();
  ns.board[idx]=(isPro(p)?"+":"")+flipped; commit(ns);
}
function editDelete(idx){
  const ns=next(); ns.board[idx]=""; sel=null; commit(ns);
}
function editClear(){
  const ns=next(true); ns.board=Array(81).fill(""); ns.hands={b:{},w:{}}; ns.last=null; sel=null; commit(ns);
}
function editInit(){
  const ns=next(true); ns.board=initialBoard(); ns.hands={b:{},w:{}}; ns.last=null; sel=null; commit(ns);
}
function editDone(){
  const ns=next(true); ns.moves=[]; ns.last=null; ns.result=null;
  editing=false; sel=null; commit(ns);
}

/* ---------- 入力 ---------- */
function onSquare(a){
  if(readOnly) return;
  const p=S.board[a];
  if(editing){
    if(sel&&sel.type==="pal"){ editPlace(a,sel.piece); return; }
    if(sel&&sel.type==="board"){
      if(sel.idx===a){ sel=null; render(); return; }
      editMove(sel.idx,a); return;
    }
    if(p){ sel={type:"board",idx:a}; render(); }
    return;
  }
  if(S.result) return;
  if(lionStep){
    const lion=S.board[lionStep.at];
    if(a===lionStep.at){ lionStop(); return; }
    if(lion&&cheb(a,lionStep.at)===1&&!(p&&owner(p)===owner(lion))){ lionSecond(a); return; }
    lionStep=null; sel=null;   // 2歩目をやめて、通常の選択として扱う
  }
  if(sel&&sel.type==="board"){
    if(sel.idx===a){ sel=null; render(); return; }
    const mover=S.board[sel.idx];
    if(p&&owner(p)===owner(mover)){ sel={type:"board",idx:a}; render(); return; }
    if(base(mover)==="X"&&cheb(sel.idx,a)===1){ lionFirst(sel.idx,a); return; }
    doMove(sel.idx,a); return;
  }
  if(sel&&sel.type==="hand"){
    if(!p){ doDrop(sel.owner,sel.piece,a); return; }
    sel={type:"board",idx:a}; render(); return;
  }
  if(p){ sel={type:"board",idx:a}; render(); }
}
function onHandPiece(o,k,ev){
  ev.stopPropagation(); if(readOnly) return;
  if(editing){
    if(sel&&sel.type==="pal"){ editHandAdd(o,base(sel.piece)); return; }
    if(sel&&sel.type==="board"){ toHand(o,sel.idx); return; }
    editHandRemove(o,k); return;
  }
  if(S.result) return;
  if(sel&&sel.type==="board"){ toHand(o,sel.idx); return; }
  if(sel&&sel.type==="hand"&&sel.owner===o&&sel.piece===k) sel=null;
  else sel={type:"hand",owner:o,piece:k};
  render();
}
function onHandArea(o){
  if(readOnly) return;
  if(editing&&sel&&sel.type==="pal"){ editHandAdd(o,base(sel.piece)); return; }
  if(!editing&&S.result) return;
  if(sel&&sel.type==="board") toHand(o,sel.idx);
}

/* ---------- 描画 ---------- */
function komaEl(p){
  const d=document.createElement("span");
  d.className="koma "+(owner(p)===side?"up":"down")+(isPro(p)?" pro":"");
  d.textContent=label(p);
  return d;
}
function renderHand(el,o){
  el.innerHTML="";
  const who=document.createElement("span"); who.className="who"; who.textContent=sideName(o); el.appendChild(who);
  const box=document.createElement("div"); box.className="pcs";
  HAND_ORDER.forEach(k=>{
    const n=S.hands[o][k]; if(!n) return;
    const b=document.createElement("button"); b.className="hpc";
    if(sel&&sel.type==="hand"&&sel.owner===o&&sel.piece===k) b.classList.add("sel");
    b.setAttribute("aria-label",(o==="b"?"先手":"後手")+"の持ち駒 "+NAMES[k]+" "+n+"枚");
    b.appendChild(komaEl(asOwner(k,o)));
    if(n>1){ const c=document.createElement("span"); c.className="cnt"; c.textContent=n; b.appendChild(c); }
    b.onclick=ev=>onHandPiece(o,k,ev);
    box.appendChild(b);
  });
  el.appendChild(box);
  const target=(sel&&sel.type==="board"&&base(S.board[sel.idx]||"K")!=="K")||(editing&&sel&&sel.type==="pal"&&base(sel.piece)!=="K");
  el.classList.toggle("target",!!target);
  el.onclick=()=>onHandArea(o);
}
function renderPalette(){
  const pal=$("palette"); pal.innerHTML="";
  [side,side==="b"?"w":"b"].forEach(o=>{
    const row=document.createElement("div"); row.className="palrow";
    const who=document.createElement("span"); who.className="who"; who.textContent=o==="b"?"☗":"☖"; row.appendChild(who);
    PALETTE.forEach(k=>{
      const p=asOwner(k,o);
      const b=document.createElement("button"); b.className="hpc";
      if(sel&&sel.type==="pal"&&sel.piece===p) b.classList.add("sel");
      b.setAttribute("aria-label",(o==="b"?"先手の":"後手の")+label(p)+"を置く");
      b.appendChild(komaEl(p));
      b.onclick=()=>{ sel=(sel&&sel.type==="pal"&&sel.piece===p)?null:{type:"pal",piece:p}; render(); };
      row.appendChild(b);
    });
    pal.appendChild(row);
  });
}
function render(){
  const chkB=checkedKings(S.board,"b"), chkW=checkedKings(S.board,"w");
  const chk=S.variant==="free"?[]:chkB.concat(chkW);
  if(lionStep&&(!S.board[lionStep.at]||base(S.board[lionStep.at])!=="X"||S.result||editing)) lionStep=null;
  const canSq=new Set();
  if(lionStep){
    const lo=owner(S.board[lionStep.at]);
    for(let t=0;t<81;t++) if(cheb(t,lionStep.at)===1&&!(S.board[t]&&owner(S.board[t])===lo)) canSq.add(t);
  }

  const board=$("board"); board.innerHTML="";
  for(let v=0;v<81;v++){
    const a=side==="b"?v:80-v;
    const b=document.createElement("button"); b.className="sq";
    const p=S.board[a];
    b.setAttribute("aria-label",coord(a)+(p?" "+(owner(p)==="b"?"先手":"後手")+label(p):" 空き"));
    if(S.last&&S.last.to===a) b.classList.add("last");
    if(sel&&sel.type==="board"&&sel.idx===a) b.classList.add("sel");
    if(chk.includes(a)) b.classList.add("chk");
    if(canSq.has(a)){ b.classList.add("can"); if(p) b.classList.add("occ"); }
    if(p) b.appendChild(komaEl(p));
    b.onclick=()=>onSquare(a);
    board.appendChild(b);
  }
  [[3,3],[3,6],[6,3],[6,6]].forEach(([r,c])=>{
    const s=document.createElement("span"); s.className="star";
    s.style.left=(c/9*100)+"%"; s.style.top=(r/9*100)+"%"; board.appendChild(s);
  });
  $("files").innerHTML=Array.from({length:9},(_,i)=>"<span>"+(side==="b"?9-i:i+1)+"</span>").join("");
  $("ranks").innerHTML=Array.from({length:9},(_,i)=>"<span>"+KAN[side==="b"?i:8-i]+"</span>").join("");
  renderHand($("handTop"),side==="b"?"w":"b");
  renderHand($("handBottom"),side);

  const n=S.moves.length, turnEl=$("turn");
  turnEl.textContent=(n%2===0?"☗ 先手の番":"☖ 後手の番")+"　"+(n+1)+"手目";
  if(!S.result&&S.variant!=="free"&&(chkB.length||chkW.length)){
    const c=document.createElement("span"); c.className="chkchip";
    c.textContent=(chkB.length?"先手":"後手")+"に王手"; turnEl.appendChild(c);
  }

  $("banner").hidden=!S.result||editing;
  if(S.result) $("bannerText").textContent=S.result.t;
  $("bannerUndo").disabled=readOnly||!S.hist.length;
  $("bannerNew").disabled=readOnly;
  $("editbar").hidden=!editing;

  document.querySelectorAll("#variants button").forEach(b=>{
    b.setAttribute("aria-pressed",String(b.dataset.v===S.variant)); b.disabled=readOnly;
  });
  $("ruleHelp").textContent=RULE_HELP[S.variant]||"";

  $("editOff").hidden=editing; $("editOn").hidden=!editing;
  $("btnEdit").disabled=readOnly;
  if(editing) renderPalette();
  const selP=sel&&sel.type==="board"?S.board[sel.idx]:null;
  $("btnOwner").disabled=!selP; $("btnDelete").disabled=!selP;

  const k=$("kifu"); k.innerHTML="";
  if(!n){ const li=document.createElement("li"); li.className="empty"; li.textContent="まだ指していません"; k.appendChild(li); }
  S.moves.forEach((m,i)=>{
    const li=document.createElement("li");
    const sp=document.createElement("span"); sp.textContent=i+1; li.appendChild(sp);
    li.appendChild(document.createTextNode(m.n)); k.appendChild(li);
  });
  k.scrollTop=k.scrollHeight;

  $("btnPromote").disabled=readOnly||!selP||(!isPro(selP)&&!PROMOTABLE.includes(base(selP)));
  $("btnUndo").disabled=readOnly||!S.hist.length;
  $("btnReset").disabled=readOnly;
  if(promo&&!readOnly&&!editing){ $("promo").hidden=false; $("promoText").textContent=coord(promo.to)+"の"+label(promo.piece)+"、成りますか？"; }
  else $("promo").hidden=true;
  $("lionBar").hidden=!(lionStep&&!readOnly);
}

/* ---------- 同期 ----------
   firebase-config.js が設定されていれば Firebase Realtime Database の rooms/<部屋名> で同期。
   未設定ならこのブラウザの中だけで保存する。 */
const FIREBASE_SDK="10.12.2";
function setStatus(kind,text){ $("dot").className="dot "+(kind||""); $("statusText").textContent=text; }
function toDoc(s){
  return {board:s.board.join(","), hands:s.hands, moves:s.moves, last:s.last||null, hist:s.hist,
    rev:s.rev||0, by:s.by||"", variant:s.variant||"hon", result:s.result||null};
}
function fromDoc(d){
  if(!d) return null;
  const board=typeof d.board==="string"?d.board.split(","):d.board;
  if(!Array.isArray(board)||board.length!==81) return null;
  const hb=d.hands&&d.hands.b, hw=d.hands&&d.hands.w;
  return {board:board.map(x=>x||""), hands:{b:Object.assign({},hb),w:Object.assign({},hw)},
    moves:Array.isArray(d.moves)?d.moves.map(m=>({n:String(m.n),to:m.to})):[], last:d.last||null,
    hist:Array.isArray(d.hist)?d.hist.slice():[], rev:d.rev||0, by:d.by||"",
    variant:["hon","oute","free"].includes(d.variant)?d.variant:"hon",
    result:d.result&&d.result.t?{w:d.result.w,t:String(d.result.t)}:null};
}
const ROOM=(()=>{
  const u=new URL(location.href); let r=u.searchParams.get("room");
  if(!r||!/^[A-Za-z0-9_-]{4,40}$/.test(r)){
    r=Math.random().toString(36).slice(2,10);
    u.searchParams.set("room",r); history.replaceState(null,"",u);
  }
  return r;
})();
let remote=null;
function saveLocal(){ try{ localStorage.setItem("shogi-room-"+ROOM,JSON.stringify(toDoc(S))); }catch(e){} }
function loadLocal(){ try{ const ns=fromDoc(JSON.parse(localStorage.getItem("shogi-room-"+ROOM))); if(ns) S=ns; }catch(e){} }
function applyRemote(ns){
  S=ns;
  if(sel&&sel.type==="board"&&!S.board[sel.idx]) sel=null;
  if(sel&&sel.type==="hand"&&!(S.hands[sel.owner]||{})[sel.piece]) sel=null;
  if(promo&&S.board[promo.to]!==promo.piece) promo=null;
  render();
}
async function flush(){
  if(!remote){ saveLocal(); return; }
  if(readOnly) return;
  if(writing){ dirty=true; return; }
  writing=true;
  do{
    dirty=false;
    try{ await remote.write(toDoc(S)); setStatus("on","同期中（リアルタイム）"); }
    catch(e){
      if(String(e&&e.code||e).toUpperCase().includes("PERMISSION")){
        readOnly=true; editing=false; setStatus("warn","書き込みが拒否されました（データベースのルールを確認してください）"); render();
      }else setStatus("warn","保存できませんでした。通信を確認してもう一度動かしてください");
    }
  }while(dirty);
  writing=false;
  if(pendingRemote){ const p=pendingRemote; pendingRemote=null; if(p.by!==CLIENT) applyRemote(p); }
}
async function connect(){
  $("roomName").textContent=ROOM;
  let cfg=null;
  try{ cfg=(await import("./firebase-config.js")).FIREBASE_CONFIG; }catch(e){}
  if(!cfg||!cfg.apiKey||!cfg.databaseURL){
    loadLocal(); render(); setStatus("warn","ローカルのみ（Firebase未設定）"); return;
  }
  try{
    const {initializeApp}=await import(`https://www.gstatic.com/firebasejs/${FIREBASE_SDK}/firebase-app.js`);
    const {getDatabase,ref,onValue,set}=await import(`https://www.gstatic.com/firebasejs/${FIREBASE_SDK}/firebase-database.js`);
    const r=ref(getDatabase(initializeApp(cfg)),"rooms/"+ROOM);
    remote={write:d=>set(r,d)};
    onValue(r,snap=>{
      const ns=fromDoc(snap.val());
      if(!ns){ setStatus("on","接続済み（最初の一手で対局開始）"); return; }
      if(writing||dirty){ pendingRemote=ns; return; }
      if(!(ns.rev===S.rev&&ns.by===S.by)) applyRemote(ns);
      setStatus("on","同期中（リアルタイム）");
    },()=>setStatus("warn","読み込めませんでした（データベースのルールを確認してください）"));
  }catch(e){
    remote=null; loadLocal(); render(); setStatus("warn","Firebaseに接続できませんでした。ローカルのみで動いています");
  }
}
$("btnCopyLink").onclick=async()=>{
  const msg=$("copyMsg");
  try{ await navigator.clipboard.writeText(location.href); msg.textContent="コピーしました"; }
  catch(e){ msg.textContent=location.href; }
  setTimeout(()=>{ if(msg.textContent==="コピーしました") msg.textContent=""; },2000);
};

/* ---------- ボタン ---------- */
$("btnFlip").onclick=()=>{ side=side==="b"?"w":"b"; try{localStorage.setItem("shogi-side",side)}catch(e){} render(); };
$("btnPromote").onclick=()=>{ if(sel&&sel.type==="board") togglePromote(sel.idx); };
$("btnUndo").onclick=undo;
$("bannerUndo").onclick=undo;
$("btnReset").onclick=()=>{ $("confirm").hidden=false; };
$("bannerNew").onclick=newGame;
$("confirmNo").onclick=()=>{ $("confirm").hidden=true; };
$("confirmYes").onclick=()=>{ $("confirm").hidden=true; newGame(); };
$("promoYes").onclick=()=>answerPromo(true);
$("promoNo").onclick=()=>answerPromo(false);
$("lionStop").onclick=lionStop;
document.querySelectorAll("#variants button").forEach(b=>b.onclick=()=>{ if(!readOnly) setVariant(b.dataset.v); });
$("btnEdit").onclick=()=>{ if(readOnly) return; editing=true; sel=null; promo=null; lionStep=null; render(); };
$("btnEditDone").onclick=editDone;
$("btnOwner").onclick=()=>{ if(sel&&sel.type==="board") editFlipOwner(sel.idx); };
$("btnDelete").onclick=()=>{ if(sel&&sel.type==="board") editDelete(sel.idx); };
$("btnClear").onclick=editClear;
$("btnInit").onclick=editInit;
document.addEventListener("keydown",e=>{ if(e.key==="Escape"){ sel=null; render(); } });

render();
connect();
})();
