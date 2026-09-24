//ENGINE-START
const SHN={M:'เช้า',A:'บ่าย',N:'ดึก'}, SHC={M:'ช',A:'บ',N:'ด'}, DISP=['M','A','N'];
const TH_MONTHS=['มกราคม','กุมภาพันธ์','มีนาคม','เมษายน','พฤษภาคม','มิถุนายน','กรกฎาคม','สิงหาคม','กันยายน','ตุลาคม','พฤศจิกายน','ธันวาคม'];
const TH_DOW=['อา','จ','อ','พ','พฤ','ศ','ส'];
const FIXED_HOL={'1-1':'วันขึ้นปีใหม่','4-6':'วันจักรี','4-13':'วันสงกรานต์','4-14':'วันสงกรานต์','4-15':'วันสงกรานต์','5-4':'วันฉัตรมงคล','6-3':'วันเฉลิมฯ พระราชินี','7-28':'วันเฉลิมฯ ร.10','8-12':'วันแม่แห่งชาติ','10-13':'วันนวมินทรมหาราช','10-23':'วันปิยมหาราช','12-5':'วันพ่อแห่งชาติ','12-10':'วันรัฐธรรมนูญ','12-31':'วันสิ้นปี'};

function defState(){
  const now=new Date(); let y=now.getFullYear(), m=now.getMonth()+1; if(m>11){m=0;y++;}
  return {y,m,
    req:{wd:{M:[2,0],A:[1,1],N:[1,1]},hd:{M:[2,1],A:[1,1],N:[1,1]}},
    rules:{maxConsec:5,countReg:true,countRef:true,maxPerDay:1,allowCont:false,nightFirst:true,countFix:false,fixExtra:true},
    staff:Array.from({length:12},(_,i)=>({id:'s'+(i+1),name:'พยาบาล '+(i+1),refer:true,max:''})),
    seq:13, leaves:{}, hol:{}, sched:{}, off:{}, ded:{}, sig:{}};
}
let S=defState();
const ym=()=>S.y+'-'+S.m;
const nDays=()=>new Date(S.y,S.m+1,0).getDate();
const dow=d=>new Date(S.y,S.m,d).getDay();
const fixedHol=d=>FIXED_HOL[(S.m+1)+'-'+d]||'';
const autoHol=d=>{const w=dow(d);return w===0||w===6||!!fixedHol(d);};
function isHol(d){const o=S.hol[ym()];if(o&&o[d]!==undefined)return o[d];return autoHol(d);}
const reqOf=d=>S.req[isHol(d)?'hd':'wd'];
function lv(sid,d){const L=S.leaves[ym()];return (L&&L[sid]&&L[sid][d])||[];}
const offOf=()=>S.off[ym()]||{};
const activeStaff=()=>S.staff.filter(s=>!offOf()[s.id]);
function workDays(){let n=0;for(let d=1;d<=nDays();d++)if(!isHol(d))n++;return n;}
function dedOf(st){if(!st.fix)return 0;const o=S.ded[ym()];const v=o&&o[st.id];return (v===undefined||v===''||isNaN(+v))?workDays():Math.max(0,+v);}
// เลือกวันทำการที่คน fix ER จะลงเวรเช้า ER (กระจายสม่ำเสมอ ข้ามวันที่ขอหยุดเช้า)
function pickFix(){
  const D=nDays(),res={},cap=+S.req.wd.M[0]||0;
  for(const st of activeStaff().filter(x=>x.fix)){
    const avail=[];for(let d=1;d<=D;d++)if(!isHol(d)&&!lv(st.id,d).includes('M'))avail.push(d);
    const n=Math.min(dedOf(st),avail.length);
    for(let i=0;i<n;i++){const d=avail[Math.floor(i*avail.length/n)];const c=res[d]=res[d]||[];if(c.length<cap)c.push(st.id);}
  }
  return res;
}
function totalReq(){let R=0;for(let d=1;d<=nDays();d++){const rq=reqOf(d);DISP.forEach(s=>R+=(+rq[s][0]||0)+(+rq[s][1]||0));}return R;}
const hasMax=st=>st.max!==''&&st.max!=null&&!isNaN(+st.max);

function buildCtx(){
  const D=nDays(), order=S.rules.nightFirst?['N','M','A']:['M','A','N'];
  const oi={};order.forEach((s,i)=>oi[s]=i);
  const hol=[];for(let d=1;d<=D;d++)hol[d]=isHol(d);
  const byId={};S.staff.forEach(s=>byId[s.id]=s);
  const r=S.rules;
  return {countFix:!!r.countFix,fixExtra:!!r.fixExtra,D,order,slotOf:(d,s)=>(d-1)*3+oi[s],hol,byId,staff:activeStaff(),leave:S.leaves[ym()]||{},
    maxCont:r.allowCont?2:1,maxPerDay:+r.maxPerDay||1,
    maxConsec:(r.countReg||r.countRef)?(+r.maxConsec||0):0,countReg:!!r.countReg,countRef:!!r.countRef};
}
const counted=(ctx,t,fx)=>fx?(ctx.countFix&&ctx.countReg):(t==='reg'?ctx.countReg:ctx.countRef);
function newP(ctx){return {slots:new Set(),dayCnt:new Array(ctx.D+2).fill(0),dayCounted:new Array(ctx.D+2).fill(0),fxs:new Set(),total:0,reg:0,ref:0,fx:0,sh:{M:0,A:0,N:0},hsh:{M:0,A:0,N:0},hol:0};}
function canAssign(ctx,P,st,d,s,t){
  if(t==='ref'&&!st.refer)return false;
  const L=ctx.leave[st.id];if(L&&L[d]&&L[d].includes(s))return false;
  const sl=ctx.slotOf(d,s);if(P.slots.has(sl))return false;
  if(P.dayCnt[d]>=ctx.maxPerDay)return false;
  let l=0,hf=false;while(P.slots.has(sl-l-1)){l++;if(P.fxs.has(sl-l))hf=true;}
  let r=0;while(P.slots.has(sl+r+1)){r++;if(P.fxs.has(sl+r))hf=true;}
  if(l+r+1>((hf&&ctx.fixExtra)?Math.max(2,ctx.maxCont):ctx.maxCont))return false;
  if(ctx.maxConsec>0&&counted(ctx,t)&&P.dayCounted[d]===0){
    let a=0;while(d-a-1>=1&&P.dayCounted[d-a-1]>0)a++;
    let b=0;while(d+b+1<=ctx.D&&P.dayCounted[d+b+1]>0)b++;
    if(a+b+1>ctx.maxConsec)return false;
  }
  if(hasMax(st)&&P.total>=+st.max)return false;
  return true;
}
function addP(ctx,P,d,s,t,fx){P.slots.add(ctx.slotOf(d,s));if(!(fx&&ctx.fixExtra))P.dayCnt[d]++;if(counted(ctx,t,fx))P.dayCounted[d]++;
  if(fx){P.fx++;P.fxs.add(ctx.slotOf(d,s));return;}P.total++;P[t]++;P.sh[s]++;if(ctx.hol[d]){P.hol++;P.hsh[s]++;}}
function remP(ctx,P,d,s,t){P.slots.delete(ctx.slotOf(d,s));P.dayCnt[d]--;if(counted(ctx,t))P.dayCounted[d]--;P.total--;P[t]--;P.sh[s]--;if(ctx.hol[d]){P.hol--;P.hsh[s]--;}}
function variance(a){if(a.length<2)return 0;const m=a.reduce((x,y)=>x+y,0)/a.length;return a.reduce((x,y)=>x+(y-m)*(y-m),0)/a.length;}
function objective(ctx,Ps,un){
  const all=ctx.staff.map(s=>Ps[s.id]),nf=ctx.staff.filter(s=>!s.fix).map(s=>Ps[s.id]);
  const fxM=ctx.staff.filter(s=>s.fix).reduce((a,s)=>a+Ps[s.id].sh.M,0);
  const free=ctx.staff.filter(s=>!hasMax(s)).map(s=>Ps[s.id]);
  const refs=ctx.staff.filter(s=>s.refer).map(s=>Ps[s.id]);
  return un*1e5+fxM*15+variance(free.map(p=>p.total))*40
    +(variance(nf.map(p=>p.sh.M))+variance(nf.map(p=>p.sh.A))+variance(nf.map(p=>p.sh.N)))*10
    +variance(all.map(p=>p.hol))*12+(variance(all.map(p=>p.hsh.M))+variance(all.map(p=>p.hsh.A))+variance(all.map(p=>p.hsh.N)))*5+variance(refs.map(p=>p.ref))*10;
}
function greedy(ctx,fix){
  const Ps={};ctx.staff.forEach(s=>Ps[s.id]=newP(ctx));
  const sched={},positions=[];let un=0;
  for(let d=1;d<=ctx.D;d++){
    sched[d]={};const rq=S.req[ctx.hol[d]?'hd':'wd'];
    for(const s of DISP)sched[d][s]={reg:new Array(+rq[s][0]||0).fill(null),ref:new Array(+rq[s][1]||0).fill(null)};
    const fx=(!ctx.hol[d]&&fix[d])?fix[d].slice(0,sched[d].M.reg.length):[];
    sched[d].fix=fx;fx.forEach((id,i)=>{sched[d].M.reg[i]=id;addP(ctx,Ps[id],d,'M','reg',true);});
  }
  for(let d=1;d<=ctx.D;d++){
    for(const s of ctx.order){
      for(const t of ['ref','reg'])for(let i=0;i<sched[d][s][t].length;i++){
        if(sched[d][s][t][i])continue;
        positions.push({d,s,t,i});
        let best=null,bs=Infinity;
        for(const st of ctx.staff){
          const P=Ps[st.id];if(!canAssign(ctx,P,st,d,s,t))continue;
          let run=0;while(d-run-1>=1&&P.dayCnt[d-run-1]>0)run++;
          const sc=P.total*10+P.sh[s]*5+(ctx.hol[d]?P.hol*8:0)+(t==='ref'?P.ref*6:P.reg*3)+run*2+(st.fix&&s==='M'?30:0)+Math.random()*7;
          if(sc<bs){bs=sc;best=st;}
        }
        if(best){addP(ctx,Ps[best.id],d,s,t);sched[d][s][t][i]=best.id;}else un++;
      }
    }
  }
  return {Ps,sched,positions,unfilled:un,obj:objective(ctx,Ps,un)};
}
function improve(ctx,sol,ms){
  const {Ps,sched,positions}=sol,st=ctx.staff,byId=ctx.byId;
  let cur=sol.obj;const t0=performance.now();
  const get=p=>sched[p.d][p.s][p.t][p.i],set=(p,v)=>{sched[p.d][p.s][p.t][p.i]=v;};
  if(!positions.length||!st.length)return;
  while(performance.now()-t0<ms){
    for(let k=0;k<200;k++){
      const a=positions[Math.random()*positions.length|0],pa=get(a);
      if(!pa||Math.random()<0.55){
        const q=st[Math.random()*st.length|0];if(q.id===pa)continue;
        if(pa)remP(ctx,Ps[pa],a.d,a.s,a.t);
        if(canAssign(ctx,Ps[q.id],q,a.d,a.s,a.t)){
          addP(ctx,Ps[q.id],a.d,a.s,a.t);const un=sol.unfilled-(pa?0:1),o=objective(ctx,Ps,un);
          if(o<cur-1e-9||(Math.abs(o-cur)<1e-9&&Math.random()<0.3)){set(a,q.id);cur=o;sol.unfilled=un;continue;}
          remP(ctx,Ps[q.id],a.d,a.s,a.t);
        }
        if(pa)addP(ctx,Ps[pa],a.d,a.s,a.t);
      }else{
        const b=positions[Math.random()*positions.length|0],pb=get(b);
        if(!pb||pb===pa||(a.d===b.d&&a.s===b.s))continue;
        remP(ctx,Ps[pa],a.d,a.s,a.t);remP(ctx,Ps[pb],b.d,b.s,b.t);
        let ok=false;
        if(canAssign(ctx,Ps[pa],byId[pa],b.d,b.s,b.t)){
          addP(ctx,Ps[pa],b.d,b.s,b.t);
          if(canAssign(ctx,Ps[pb],byId[pb],a.d,a.s,a.t)){addP(ctx,Ps[pb],a.d,a.s,a.t);ok=true;}
          else remP(ctx,Ps[pa],b.d,b.s,b.t);
        }
        if(ok){
          const o=objective(ctx,Ps,sol.unfilled);
          if(o<=cur+1e-9){set(a,pb);set(b,pa);cur=o;continue;}
          remP(ctx,Ps[pb],a.d,a.s,a.t);remP(ctx,Ps[pa],b.d,b.s,b.t);
        }
        addP(ctx,Ps[pa],a.d,a.s,a.t);addP(ctx,Ps[pb],b.d,b.s,b.t);
      }
    }
  }
  sol.obj=cur;
}
function solve(msGreedy,msImprove){
  const ctx=buildCtx();let best=null;const t0=performance.now();
  const fix=pickFix();
  while(!best||performance.now()-t0<msGreedy){const s=greedy(ctx,fix);if(!best||s.obj<best.obj)best=s;}
  improve(ctx,best,msImprove);
  return best;
}
function normalize(sc){
  const D=nDays(),ids=new Set(S.staff.map(s=>s.id));
  for(let d=1;d<=D;d++){
    sc[d]=sc[d]||{};const rq=reqOf(d);
    for(const s of DISP){
      const c=sc[d][s]=sc[d][s]||{reg:[],ref:[]};
      [['reg',0],['ref',1]].forEach(([t,k])=>{
        const n=+rq[s][k]||0,arr=(c[t]||[]).slice(0,n).map(v=>ids.has(v)?v:null);
        while(arr.length<n)arr.push(null);c[t]=arr;
      });
    }
    sc[d].fix=isHol(d)?[]:(sc[d].fix||[]).filter(id=>sc[d].M.reg.includes(id));
  }
  return sc;
}
function validate(sc){
  const ctx=buildCtx(),iss={},per={};
  const push=(k,m)=>{const a=iss[k]=iss[k]||[];if(!a.includes(m))a.push(m);};
  for(let d=1;d<=ctx.D;d++)for(const s of DISP)for(const t of ['reg','ref'])sc[d][s][t].forEach((id,i)=>{
    if(!id)return;const k=`${d}|${s}|${t}|${i}`,st=ctx.byId[id];
    if(offOf()[id])push(k,'ไม่ได้ขึ้นเวรเดือนนี้');
    if(lv(id,d).includes(s))push(k,'ขอหยุดเวรนี้ไว้');
    if(t==='ref'&&!st.refer)push(k,'ไม่ได้ตั้งให้ขึ้นเวร refer');
    const fx=s==='M'&&t==='reg'&&sc[d].fix.includes(id);
    (per[id]=per[id]||[]).push({d,s,t,k,fx,sl:ctx.slotOf(d,s)});
  });
  for(const id in per){
    const L=per[id],st=ctx.byId[id];
    const bySl={},byDay={};L.forEach(x=>{(bySl[x.sl]=bySl[x.sl]||[]).push(x);(byDay[x.d]=byDay[x.d]||[]).push(x);});
    Object.values(bySl).forEach(g=>{if(g.length>1)g.forEach(x=>push(x.k,'ชื่อซ้ำในเวรเดียวกัน'));});
    Object.values(byDay).forEach(g=>{if(g.filter(x=>!(x.fx&&ctx.fixExtra)).length>ctx.maxPerDay)g.forEach(x=>push(x.k,`เกิน ${ctx.maxPerDay} เวรต่อวัน`));});
    const sls=[...new Set(L.map(x=>x.sl))].sort((a,b)=>a-b);
    for(let i=0;i<sls.length;){let j=i;while(j+1<sls.length&&sls[j+1]===sls[j]+1)j++;
      const run=new Set(sls.slice(i,j+1)),hf=L.some(x=>x.fx&&run.has(x.sl)),lim=(hf&&ctx.fixExtra)?Math.max(2,ctx.maxCont):ctx.maxCont;
      if(j-i+1>lim){const set=run;L.forEach(x=>{if(set.has(x.sl))push(x.k,lim===1?'ควบเวรต่อเนื่อง (ไม่ได้อนุญาต)':'ควบเวรต่อเนื่องเกิน 16 ชม.');});}
      i=j+1;}
    if(ctx.maxConsec>0){
      const days=[...new Set(L.filter(x=>counted(ctx,x.t,x.fx)).map(x=>x.d))].sort((a,b)=>a-b);
      for(let i=0;i<days.length;){let j=i;while(j+1<days.length&&days[j+1]===days[j]+1)j++;
        if(j-i+1>ctx.maxConsec){const set=new Set(days.slice(i,j+1));L.forEach(x=>{if(set.has(x.d)&&counted(ctx,x.t,x.fx))push(x.k,`อยู่เวรติดกันเกิน ${ctx.maxConsec} วัน`);});}
        i=j+1;}
    }
    if(hasMax(st)&&L.filter(x=>!x.fx).length>+st.max)L.filter(x=>!x.fx).forEach(x=>push(x.k,`เกินเวรสูงสุดของคนนี้ (${st.max})`));
  }
  return iss;
}
function sigNow(){const k=ym();return JSON.stringify([S.req,S.rules,S.staff.map(x=>[x.id,x.refer,x.max,!!x.fix]),S.leaves[k]||{},S.hol[k]||{},S.off[k]||{},S.ded[k]||{}]);}
function reasonOf(ctx,P,st,d,s,t){
  if(t==='ref'&&!st.refer)return 'ไม่ขึ้น refer';
  const L=ctx.leave[st.id];if(L&&L[d]&&L[d].includes(s))return 'ขอหยุด';
  const sl=ctx.slotOf(d,s);if(P.slots.has(sl))return 'อยู่เวรนี้แล้ว';
  if(P.dayCnt[d]>=ctx.maxPerDay)return P.fxs.size&&!ctx.fixExtra&&P.fxs.has(ctx.slotOf(d,'M'))?'วัน fix ER':'มีเวรวันนี้แล้ว';
  let l=0,hf=false;while(P.slots.has(sl-l-1)){l++;if(P.fxs.has(sl-l))hf=true;}
  let r=0;while(P.slots.has(sl+r+1)){r++;if(P.fxs.has(sl+r))hf=true;}
  if(l+r+1>((hf&&ctx.fixExtra)?Math.max(2,ctx.maxCont):ctx.maxCont))return 'จะควบเวร';
  if(ctx.maxConsec>0&&counted(ctx,t)&&P.dayCounted[d]===0){
    let a=0;while(d-a-1>=1&&P.dayCounted[d-a-1]>0)a++;let b=0;while(d+b+1<=ctx.D&&P.dayCounted[d+b+1]>0)b++;
    if(a+b+1>ctx.maxConsec)return `ติดกันเกิน ${ctx.maxConsec} วัน`;}
  if(hasMax(st)&&P.total>=+st.max)return 'ครบเวรสูงสุด';
  return null;
}
function diagnose(sc){
  const ctx=buildCtx(),Ps={};S.staff.forEach(st=>Ps[st.id]=newP(ctx));
  const holes=[];
  for(let d=1;d<=ctx.D;d++)for(const s of DISP)for(const t of ['reg','ref'])sc[d][s][t].forEach(id=>{
    if(!id){holes.push({d,s,t});return;}if(Ps[id])addP(ctx,Ps[id],d,s,t,s==='M'&&t==='reg'&&(sc[d].fix||[]).includes(id));});
  return {ctx,holes:holes.map(h=>({...h,why:ctx.staff.map(st=>reasonOf(ctx,Ps[st.id],st,h.d,h.s,h.t))}))};
}
function stats(sc){
  const res={};S.staff.forEach(s=>res[s.id]={wd:{M:0,A:0,N:0},hd:{M:0,A:0,N:0},reg:0,ref:0,total:0,fx:0});
  let un=0;const D=nDays();
  for(let d=1;d<=D;d++){const k=isHol(d)?'hd':'wd';for(const s of DISP)for(const t of ['reg','ref'])sc[d][s][t].forEach(id=>{
    if(!id||!res[id]){un++;return;}const r=res[id];if(s==='M'&&t==='reg'&&(sc[d].fix||[]).includes(id)){r.fx++;return;}r[k][s]++;r[t]++;r.total++;});}
  return {res,un};
}
//ENGINE-END

const $=s=>document.querySelector(s);
const view=$('#view'),pop=$('#pop');
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const SK='nurse-roster-v1';
function load(){try{const t=localStorage.getItem(SK);if(t){const o=JSON.parse(t);S=Object.assign(defState(),o);S.rules=Object.assign(defState().rules,o.rules||{});}}catch(e){}}
function save(){try{localStorage.setItem(SK,JSON.stringify(S));}catch(e){}}
let tab='setup',pview='day';
function askConfirm(msg,okLabel){
  return new Promise(res=>{
    const bg=document.createElement('div');bg.className='modal-bg';
    bg.innerHTML=`<div class="modal" role="dialog" aria-modal="true"><p>${esc(msg)}</p><div class="mbtns"><button class="btn" data-a="0">ยกเลิก</button><button class="btn primary" data-a="1">${esc(okLabel||'ตกลง')}</button></div></div>`;
    const done=v=>{bg.remove();document.removeEventListener('keydown',key);res(v);};
    const key=e=>{if(e.key==='Escape')done(false);};
    bg.addEventListener('click',e=>{e.stopPropagation();const b=e.target.closest('[data-a]');if(b)done(b.dataset.a==='1');else if(e.target===bg)done(false);});
    document.addEventListener('keydown',key);document.body.appendChild(bg);bg.querySelector('[data-a="1"]').focus();
  });
}
function toast(m){const t=$('#toast');t.textContent=m;t.classList.add('show');clearTimeout(toast.h);toast.h=setTimeout(()=>t.classList.remove('show'),2200);}

function render(){
  $('#mlabel').textContent=TH_MONTHS[S.m]+' '+(S.y+543);
  document.querySelectorAll('.tabs button').forEach(b=>b.setAttribute('aria-selected',b.dataset.tab===tab));
  pop.hidden=true;
  ({setup:renderSetup,staff:renderStaff,sched:renderSched,sum:renderSum})[tab]();
}

function renderSetup(){
  const q=S.req,r=S.rules,D=nDays();
  const row=s=>`<tr><th>${SHN[s]}</th>${['wd','hd'].map(k=>[0,1].map(t=>`<td class="${t===0?'grp':''}"><input type="number" min="0" max="9" data-req="${k}|${s}|${t}" value="${q[k][s][t]}" aria-label="${SHN[s]} ${k==='wd'?'วันธรรมดา':'วันหยุด'} ${t?'refer':'ธรรมดา'}"></td>`).join('')).join('')}</tr>`;
  let cal=TH_DOW.map(x=>`<div class="dh">${x}</div>`).join('');
  for(let i=0;i<dow(1);i++)cal+='<div></div>';
  let need=0,holN=0;
  for(let d=1;d<=D;d++){
    const h=isHol(d),nm=fixedHol(d);if(h)holN++;
    const rq=reqOf(d);DISP.forEach(s=>need+=(+rq[s][0]||0)+(+rq[s][1]||0));
    cal+=`<button class="${h?'h':''}" data-hol="${d}" aria-pressed="${h}"><b>${d}</b>${nm&&h?`<small>${nm}</small>`:''}${h&&!nm&&dow(d)%6!==0?'<small>วันหยุด</small>':''}</button>`;
  }
  const n=activeStaff().length||1;
  view.innerHTML=`
  <div class="cols">
    <section class="panel"><h2>จำนวนคนต่อเวร</h2><p class="hint">เวร refer นับแยกจากเวรธรรมดา ตั้งเป็น 0 ถ้าไม่มีเวรประเภทนั้น</p>
      <table class="req"><thead><tr><th></th><th colspan="2" class="grp">วันธรรมดา</th><th colspan="2" class="grp">วันหยุด / นักขัตฤกษ์</th></tr>
      <tr><th></th><th class="grp">ธรรมดา</th><th>refer</th><th class="grp">ธรรมดา</th><th>refer</th></tr></thead>
      <tbody>${DISP.map(row).join('')}</tbody></table>
    </section>
    <section class="panel"><h2>เงื่อนไขการจัดเวร</h2>
      <div class="rule"><span>ห้ามอยู่เวรติดต่อกันเกิน</span><input type="number" min="0" max="31" data-rule="maxConsec" value="${r.maxConsec}"><span>วัน</span><span class="note">ใส่ 0 ถ้าไม่จำกัด</span></div>
      <div class="rule"><span>นับวันต่อเนื่องจาก</span><label><input type="checkbox" data-rule="countReg" ${r.countReg?'checked':''}> เวรธรรมดา</label><label><input type="checkbox" data-rule="countRef" ${r.countRef?'checked':''}> เวร refer</label>
        <span class="note">ติ๊กทั้งสองช่อง = นับรวมกัน, ติ๊กช่องเดียว = นับเฉพาะประเภทนั้น, ไม่ติ๊กเลย = ไม่จำกัด</span></div>
      <div class="rule"><span>เวรสูงสุดต่อคนต่อวัน</span><select data-rule="maxPerDay">${[1,2].map(v=>`<option ${+r.maxPerDay===v?'selected':''}>${v}</option>`).join('')}</select></div>
      <div class="rule"><label><input type="checkbox" data-rule="allowCont" ${r.allowCont?'checked':''}> อนุญาตควบเวรต่อเนื่อง ไม่เกิน 16 ชม.</label><span class="note">เช่น บ่ายต่อดึก หรือ ดึกต่อเช้า ใช้ได้เมื่อตั้งเวรสูงสุดต่อวันเป็น 2</span></div>
      <div class="rule"><label><input type="checkbox" data-rule="fixExtra" ${r.fixExtra?'checked':''}> คน fix ER รับเวร OT ในวันที่ fix เช้าได้อีก 1 เวร</label><span class="note">เช่น เช้า fix ER แล้วต่อบ่าย หรือขึ้นดึกก่อนเช้า fix ER ต่อเนื่องไม่เกิน 16 ชม. ถ้าไม่ติ๊ก วันที่ fix เช้าจะไม่ได้รับเวรอื่น ทำให้คน fix ER ได้ OT น้อยกว่าคนอื่น</span></div>
      <div class="rule"><label><input type="checkbox" data-rule="countFix" ${r.countFix?'checked':''}> นับเวรเช้า fix ER ในการนับวันอยู่เวรติดต่อกัน</label><span class="note">ถ้าไม่ติ๊ก เวร fix ER จะไม่ถูกนับเป็นวันติดต่อกัน (ใช้เมื่อนับเวรธรรมดาอยู่)</span></div>
      <div class="rule"><span>เวรดึกของวันที่ในตาราง</span><select data-rule="nightFirst"><option value="1" ${r.nightFirst?'selected':''}>เริ่ม 00.00 น. ของวันนั้น (ดึก → เช้า → บ่าย)</option><option value="0" ${!r.nightFirst?'selected':''}>เริ่ม 24.00 น. ของวันนั้น (เช้า → บ่าย → ดึก)</option></select></div>
    </section>
  </div>
  <div class="cols" style="margin-top:18px">
    <section class="panel"><h2>สำรองข้อมูล</h2><p class="hint">ข้อมูลทั้งหมดเก็บในเบราว์เซอร์เครื่องนี้เท่านั้น ดาวน์โหลดไฟล์สำรองไว้ แล้วนำเข้าเมื่อเปลี่ยนเครื่องหรือเปลี่ยนเบราว์เซอร์</p>
      <div class="bar" style="margin:0"><button class="btn" id="backup">ดาวน์โหลดไฟล์สำรอง</button><label class="btn" for="restoreFile">นำเข้าไฟล์สำรอง</label><input type="file" id="restoreFile" accept=".json,application/json" hidden></div></section>
    <section class="panel"><h2>หัวกระดาษเอกสาร</h2><p class="hint">ชื่อหน่วยงานที่จะแสดงในไฟล์ Excel และ PDF เว้นว่างได้</p>
      <input type="text" class="unit" data-unit value="${esc(S.unit||'')}" placeholder="เช่น งานอุบัติเหตุและฉุกเฉิน โรงพยาบาล..." aria-label="ชื่อหน่วยงาน"></section>
  </div>
  <div class="cols" style="margin-top:18px">
    <section class="panel"><h2>วันหยุดของเดือน</h2><p class="hint">เสาร์-อาทิตย์และวันหยุดราชการที่วันที่ตายตัวถูกตั้งไว้แล้ว แตะวันเพื่อสลับเป็นวันหยุด/วันทำการ เช่น เพิ่มวันหยุดทางพุทธศาสนาหรือวันหยุดชดเชย</p>
      <div class="cal">${cal}</div></section>
    <section class="panel"><h2>ภาระงานเดือนนี้</h2><p class="hint">ใช้ประเมินว่าจำนวนเจ้าหน้าที่พอหรือไม่</p>
      <div class="cap"><div><b>${need}</b><span>เวรที่ต้องจัดทั้งเดือน</span></div><div><b>${holN}</b><span>วันหยุด</span></div><div><b>${activeStaff().length}</b><span>พยาบาลที่ขึ้นเวร</span></div><div><b>${(need/n).toFixed(1)}</b><span>เวรเฉลี่ยต่อคน</span></div></div>
    </section>
  </div>`;
}

function lvText(a){if(!a.length)return'';if(a.length===3)return'หยุด';return DISP.filter(s=>a.includes(s)).map(s=>SHC[s]).join(' ');}
function dayHead(d){const h=isHol(d);return `<th class="${h?'hol':''}"><div>${d}</div><div style="font-size:.72rem">${TH_DOW[dow(d)]}</div></th>`;}
function renderStaff(){
  const D=nDays(),off=offOf(),act=activeStaff().length;
  let head='<th class="stick" style="text-align:left;padding-left:12px">เจ้าหน้าที่</th>';for(let d=1;d<=D;d++)head+=dayHead(d);
  const rows=S.staff.map(st=>{
    const isOff=!!off[st.id];
    let c=`<th class="stick namecell"><input type="text" data-sname="${st.id}" value="${esc(st.name)}" aria-label="ชื่อเจ้าหน้าที่">
      <div class="opts"><label><input type="checkbox" data-son="${st.id}" ${isOff?'':'checked'}> ขึ้นเวรเดือนนี้</label>
      <label><input type="checkbox" data-sref="${st.id}" ${st.refer?'checked':''}> refer</label>
      <label><input type="checkbox" data-sfix="${st.id}" ${st.fix?'checked':''}> fix เช้า ER</label>
      ${st.fix?`<label>อย่างน้อย <input type="number" min="0" max="31" data-sded="${st.id}" value="${dedOf(st)}" aria-label="จำนวนวันเช้า fix ER ขั้นต่ำ"> วัน</label>`:''}
      <button class="nom" data-snom="${st.id}|M" aria-pressed="${noShift(st.id,'M')}" title="ขอไม่อยู่เวรเช้าทุกวันธรรมดาของเดือนนี้ กดอีกครั้งเพื่อยกเลิก">ไม่อยู่เช้าวันธรรมดา</button>
      <button class="nom" data-snom="${st.id}|N" aria-pressed="${noShift(st.id,'N')}" title="ขอไม่อยู่เวรดึกทุกวันธรรมดาของเดือนนี้ กดอีกครั้งเพื่อยกเลิก">ไม่อยู่ดึกวันธรรมดา</button>
      <label>สูงสุด <input type="number" min="0" data-smax="${st.id}" value="${esc(st.max)}" placeholder="–" aria-label="เวรสูงสุดต่อเดือน"></label>
      <button class="del" data-sdel="${st.id}" aria-label="ลบ ${esc(st.name)}">✕</button></div></th>`;
    for(let d=1;d<=D;d++){const a=lv(st.id,d);
      c+=isOff?`<td class="lvoff ${isHol(d)?'hol':''}"></td>`:`<td class="lv ${isHol(d)?'hol':''} ${a.length===3?'full':''}" data-lv="${st.id}|${d}" tabindex="0">${lvText(a)}</td>`;}
    return `<tr class="${isOff?'offrow':''}">${c}</tr>`;}).join('');
  view.innerHTML=`<section class="panel"><h2>จำนวนพยาบาล</h2>
    <p class="hint">ตั้งจำนวนพยาบาลทั้งหมดในรายชื่อ แล้วติ๊ก "ขึ้นเวรเดือนนี้" เฉพาะคนที่ใช้จัดเวรใน${TH_MONTHS[S.m]} คนที่ไม่ได้ติ๊กจะยังอยู่ในรายชื่อสำหรับเดือนอื่น</p>
    <div class="rule"><span>พยาบาลทั้งหมด</span><input type="number" min="0" max="60" id="staffCount" value="${S.staff.length}"><span>คน</span>
    <span style="margin-left:14px">ขึ้นเวรเดือนนี้ <b>${act}</b> คน</span>
    <button class="btn" id="allOn">เลือกทุกคน</button><button class="btn" id="allOff">ไม่เลือกทุกคน</button></div>${fixInfo()}</section>
    <div class="bar"><button class="btn primary" id="addStaff">เพิ่มเจ้าหน้าที่ 1 คน</button><button class="btn" id="clrLeave">ล้างวันขอหยุดเดือนนี้</button>
    <span class="status">แตะช่องวันที่เพื่อบันทึกวันขอหยุด เลือกได้ทั้งวันหรือเฉพาะเวร ช / บ / ด ปุ่ม "ไม่อยู่เช้าวันธรรมดา" และ "ไม่อยู่ดึกวันธรรมดา" ขอหยุดเวรนั้นทุกวันธรรมดาของเดือนนี้ในครั้งเดียว ช่อง "สูงสุด" คือจำนวนเวรมากที่สุดที่คนนั้นรับได้ในเดือน (เว้นว่าง = ไม่จำกัด)</span></div>
    ${S.staff.length?`<div class="wrap"><table class="g"><thead><tr>${head}</tr></thead><tbody>${rows}</tbody></table></div>`:`<div class="panel empty-state"><b>ยังไม่มีรายชื่อเจ้าหน้าที่</b>ใส่จำนวนพยาบาลด้านบน หรือกด "เพิ่มเจ้าหน้าที่ 1 คน"</div>`}`;
}
function fixInfo(){
  const act=activeStaff(),fx=act.filter(st=>st.fix),fix=pickFix(),R=totalReq();
  const cnt={};Object.values(fix).forEach(a=>a.forEach(id=>cnt[id]=(cnt[id]||0)+1));
  const F=Object.values(cnt).reduce((a,b)=>a+b,0),rest=R-F,avg=act.length?rest/act.length:0;
  return `<div class="fixbox"><p class="hint" style="margin:0 0 6px">คนที่ติ๊ก "fix เช้า ER" จะถูกลงเวรเช้าวันทำการอย่างน้อยตามจำนวนวันที่ระบุ (ค่าเริ่มต้น = วันทำการของเดือน ${workDays()} วัน ข้ามวันที่ขอหยุดเช้า) เวรจำนวนนี้ไม่นับรวมตอนเฉลี่ย ส่วนเวรอื่นทั้งหมด รวมทั้งเวรเช้าวันทำการที่เกินจากจำนวนที่ระบุ บ่าย ดึก และวันหยุด นับรวมและแบ่งให้ทุกคนเท่ากัน คน fix ก็ได้รับเวรเหล่านี้ด้วย</p>
  <p style="margin:0">เวรทั้งหมด ${R} เวร ${F?`หัก fix ER ${F} เวร (${fx.map(st=>`${esc(st.name)} ${cnt[st.id]||0}`).join(', ')}) เหลือ ${rest} เวร`:''} เฉลี่ยคนละประมาณ <b>${avg.toFixed(1)}</b> เวร</p></div>`;
}
function noShift(sid,sh){let n=0;for(let d=1;d<=nDays();d++){if(isHol(d))continue;n++;if(!lv(sid,d).includes(sh))return false;}return n>0;}
function toggleNoShift(sid,sh){
  const on=!noShift(sid,sh),L=S.leaves[ym()]=S.leaves[ym()]||{},P=L[sid]=L[sid]||{};
  for(let d=1;d<=nDays();d++){if(isHol(d))continue;let a=(P[d]||[]).filter(x=>x!==sh);if(on)a=[...a,sh];if(a.length)P[d]=a;else delete P[d];}
  save();renderStaff();toast(on?`ขอไม่อยู่เวร${SHN[sh]}ทุกวันธรรมดาของเดือนนี้แล้ว`:`ยกเลิกขอหยุดเวร${SHN[sh]}วันธรรมดาแล้ว`);
}
function shownStaff(sc){
  const used=new Set();if(sc)for(const d in sc)for(const s of DISP)for(const t of ['reg','ref'])(sc[d][s]?.[t]||[]).forEach(id=>id&&used.add(id));
  const off=offOf();return S.staff.filter(st=>!off[st.id]||used.has(st.id));
}
async function setStaffCount(n){
  n=Math.max(0,Math.min(60,n|0));
  if(n>S.staff.length){while(S.staff.length<n){const id='s'+(S.seq++);S.staff.push({id,name:'พยาบาล '+(S.staff.length+1),refer:true,max:''});}}
  else if(n<S.staff.length){
    const gone=S.staff.slice(n);
    if(!await askConfirm(`ลบ ${gone.length} คนท้ายรายชื่อ (${gone.map(g=>g.name).join(', ')}) ออกจากทุกเดือน?`,'ลบออก')){renderStaff();return;}
    S.staff=S.staff.slice(0,n);
  }
  save();renderStaff();
}
function openPop(cell){
  const [sid,ds]=cell.dataset.lv.split('|'),d=+ds,st=S.staff.find(s=>s.id===sid);if(!st)return;
  const a=lv(sid,d);
  pop.innerHTML=`<h3>${esc(st.name)} ขอหยุดวันที่ ${d}</h3>
    <div class="row">${DISP.map(s=>`<button data-pl="${s}" class="${a.includes(s)?'on':''}">${SHN[s]}</button>`).join('')}</div>
    <div class="wide"><button data-pl="ALL" class="${a.length===3?'on':''}">ทั้งวัน</button><button data-pl="CLR">ไม่หยุด</button></div>`;
  pop.dataset.cell=cell.dataset.lv;pop.hidden=false;
  const r=cell.getBoundingClientRect(),w=228;
  let left=r.left+window.scrollX+r.width/2-w/2;left=Math.max(8,Math.min(left,window.scrollX+document.documentElement.clientWidth-w-8));
  pop.style.left=left+'px';pop.style.top=(r.bottom+window.scrollY+6)+'px';
}
function setLeave(sid,d,arr){
  const L=S.leaves[ym()]=S.leaves[ym()]||{},P=L[sid]=L[sid]||{};
  if(arr.length)P[d]=arr;else delete P[d];save();
  const cell=view.querySelector(`[data-lv="${sid}|${d}"]`);
  if(cell){cell.textContent=lvText(arr);cell.classList.toggle('full',arr.length===3);openPop(cell);}
}

function renderSched(){
  const sc=S.sched[ym()];
  const bar=`<div class="bar"><button class="btn primary" id="gen">${sc?'จัดเวรใหม่ทั้งเดือน':'จัดเวรอัตโนมัติ'}</button>
    ${sc?`<div class="seg" role="group" aria-label="มุมมอง"><button data-pv="day" aria-pressed="${pview==='day'}">รายวัน</button><button data-pv="person" aria-pressed="${pview==='person'}">รายบุคคล</button></div>
    ${DL?'<button class="btn exp" id="xlsx">ส่งออก Excel</button><button class="btn exp" id="pdf">ส่งออก PDF</button>':''}<button class="btn" id="copy">คัดลอกไปวางใน Excel</button><button class="btn" id="clrSched">ล้างตาราง</button>`:''}
    <span class="status" id="st"></span></div>`;
  if(!sc){view.innerHTML=bar+`<div class="panel empty-state"><b>ยังไม่มีตารางเวรของเดือนนี้</b>ตรวจรายชื่อ วันขอหยุด และเงื่อนไขให้เรียบร้อย แล้วกด "จัดเวรอัตโนมัติ"</div>`;return;}
  normalize(sc);
  const iss=validate(sc),{un}=stats(sc),nIss=Object.keys(iss).length;
  const status=(un?`<span class="bad">ว่าง ${un} ตำแหน่ง</span> `:'')+(nIss?`<span class="bad">ผิดเงื่อนไข ${nIss} ช่อง</span> (ชี้ที่ช่องขอบแดงเพื่อดูสาเหตุ)`:'')+(!un&&!nIss?'<span class="good">ครบทุกเวรและผ่านทุกเงื่อนไข</span>':'');
  const D=nDays(),keep=view.querySelector('.wrap');const sx=keep?keep.scrollLeft:0,sy=keep?keep.scrollTop:0;
  let html;
  if(pview==='day'){
    const cols={};DISP.forEach(s=>cols[s]={reg:Math.max(+S.req.wd[s][0]||0,+S.req.hd[s][0]||0),ref:Math.max(+S.req.wd[s][1]||0,+S.req.hd[s][1]||0)});
    let h1='<th class="stick" rowspan="2">วันที่</th>',h2='';
    DISP.forEach(s=>{const n=cols[s].reg+cols[s].ref;if(!n)return;h1+=`<th colspan="${n}" class="sh-${s}">${SHN[s]}</th>`;
      for(let i=0;i<cols[s].reg;i++)h2+=`<th>ธรรมดา</th>`;for(let i=0;i<cols[s].ref;i++)h2+=`<th class="t-ref">refer</th>`;});
    const act=activeStaff(),opts=act.map(st=>`<option value="${st.id}">${esc(st.name)}</option>`).join('');
    let body='';
    for(let d=1;d<=D;d++){
      const h=isHol(d),nm=fixedHol(d);
      let r=`<th class="stick dcell ${h?'hol':''}"><b>${d}</b> <span>${TH_DOW[dow(d)]}</span>${nm&&h?`<em>${nm}</em>`:''}</th>`;
      DISP.forEach(s=>{for(const t of ['reg','ref'])for(let i=0;i<cols[s][t];i++){
        const arr=sc[d][s][t];
        if(i>=arr.length){r+=`<td class="na"></td>`;continue;}
        const v=arr[i],k=`${d}|${s}|${t}|${i}`,is=iss[k],fxc=v&&s==='M'&&t==='reg'&&sc[d].fix.includes(v);
        r+=`<td class="c ${s} ${t} ${fxc?'fx':''} ${v?'':'empty'} ${is?'bad':''}" ${is?`title="${esc(is.join(', '))}"`:''}><select data-pos="${k}" aria-label="วันที่ ${d} ${SHN[s]} ${t==='ref'?'refer':'ธรรมดา'}"><option value="">ว่าง</option>${!v?opts:act.some(x=>x.id===v)?opts.replace(`value="${v}"`,`value="${v}" selected`):`<option value="${v}" selected>${esc(S.staff.find(x=>x.id===v)?.name)} (ไม่ได้ขึ้นเวร)</option>`+opts}</select></td>`;
      }});
      body+=`<tr>${r}</tr>`;
    }
    html=`<div class="wrap"><table class="g"><thead><tr>${h1}</tr><tr>${h2}</tr></thead><tbody>${body}</tbody></table></div>
    <div class="legend"><span><span class="k M">ช</span>เช้า</span><span><span class="k A">บ</span>บ่าย</span><span><span class="k N">ด</span>ดึก</span><span>ขีดแดงซ้ายช่อง = เวร refer</span><span>ป้าย fix ER = เวรเช้า ER ประจำ ไม่นับเฉลี่ย</span><span>เลือกชื่อในช่องเพื่อแก้ไขเองได้</span></div>`;
  }else{
    let head='<th class="stick" style="text-align:left;padding-left:12px">เจ้าหน้าที่</th>';for(let d=1;d<=D;d++)head+=dayHead(d);head+='<th>OT (นับเฉลี่ย)</th>';
    const {res}=stats(sc);
    const body=shownStaff(sc).map(st=>{
      let r=`<th class="stick dcell" style="min-width:150px">${esc(st.name)}${st.fix?' <span class="tag">fix ER</span>':''}</th>`;
      for(let d=1;d<=D;d++){let c='';
        DISP.forEach(s=>['reg','ref'].forEach(t=>{if(sc[d][s][t].includes(st.id))c+=(s==='M'&&t==='reg'&&sc[d].fix.includes(st.id))?`<span class="k fxk">ER</span>`:`<span class="k ${s} ${t}">${SHC[s]}</span>`;}));
        if(!c&&lv(st.id,d).length)c='<span class="off">ขอหยุด</span>';
        r+=`<td class="pv ${isHol(d)?'hol':''}">${c}</td>`;}
      return `<tr>${r}<td class="num tot">${res[st.id].total}${res[st.id].fx?` <span class="off">+${res[st.id].fx} ER</span>`:''}</td></tr>`;}).join('');
    html=`<div class="wrap"><table class="g"><thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>
    <div class="legend"><span><span class="k M">ช</span>เช้า</span><span><span class="k A">บ</span>บ่าย</span><span><span class="k N">ด</span>ดึก</span><span><span class="k A ref">บ</span>กรอบแดง = เวร refer</span><span><span class="k fxk">ER</span>เช้า fix ER (ไม่นับเฉลี่ย)</span></div>`;
  }
  const stale=!(S.sig&&S.sig[ym()])||S.sig[ym()]!==sigNow();
  view.innerHTML=bar+(stale?`<div class="panel stale"><b>ตารางนี้จัดไว้ก่อนการแก้ไขล่าสุด (รายชื่อ วันขอหยุด เงื่อนไข หรือเวอร์ชันของโปรแกรม)</b> ตารางด้านล่างยังเป็นแบบเดิม กด "จัดเวรใหม่ทั้งเดือน" เพื่อใช้ค่าล่าสุด</div>`:'')+html;$('#st').innerHTML=status;
  const w=view.querySelector('.wrap');if(w){w.scrollLeft=sx;w.scrollTop=sy;}
}

function renderSum(){
  const sc=S.sched[ym()];
  if(!sc){view.innerHTML=`<div class="panel empty-state"><b>ยังไม่มีตารางเวรของเดือนนี้</b>ไปที่แท็บ "ตารางเวร" แล้วกดจัดเวรอัตโนมัติ</div>`;return;}
  normalize(sc);const {res,un}=stats(sc),D=nDays();
  const tot={wd:{M:0,A:0,N:0},hd:{M:0,A:0,N:0},reg:0,ref:0,total:0,lv:0,ded:0};
  const rows=shownStaff(sc).map(st=>{const r=res[st.id];let lvn=0;for(let d=1;d<=D;d++)lvn+=lv(st.id,d).length;
    DISP.forEach(s=>{tot.wd[s]+=r.wd[s];tot.hd[s]+=r.hd[s];});tot.reg+=r.reg;tot.ref+=r.ref;tot.total+=r.total;tot.lv+=lvn;const dd=r.fx;tot.ded+=dd;
    return `<tr><th class="stick dcell" style="min-width:150px">${esc(st.name)}${st.fix?' <span class="tag">fix ER</span>':''}</th>${DISP.map(s=>`<td class="num">${r.wd[s]}</td>`).join('')}${DISP.map(s=>`<td class="num hol">${r.hd[s]}</td>`).join('')}<td class="num">${r.reg}</td><td class="num">${r.ref}</td><td class="num tot">${r.total}</td><td class="num">${dd||''}</td><td class="num tot">${r.total+dd}</td><td class="num">${lvn}</td></tr>`;}).join('');
  const n=shownStaff(sc).length||1;
  view.innerHTML=`<div class="bar">${DL?'<button class="btn exp" id="xlsx">ส่งออก Excel</button><button class="btn exp" id="pdf">ส่งออก PDF</button>':''}<button class="btn" id="copySum">คัดลอกสรุปไปวางใน Excel</button><span class="status">${un?`<span class="bad">ยังมีเวรว่าง ${un} ตำแหน่ง</span>`:'จัดเวรครบทุกตำแหน่ง'} OT เฉลี่ย ${(tot.total/n).toFixed(1)} เวรต่อคน</span></div>
  <div class="wrap"><table class="g"><thead>
    <tr><th class="stick" rowspan="2" style="text-align:left;padding-left:12px">เจ้าหน้าที่</th><th colspan="3">วันธรรมดา</th><th colspan="3" class="hol">วันหยุด / นักขัตฤกษ์</th><th colspan="2">ประเภทเวร</th><th rowspan="2">OT<br>(นับเฉลี่ย)</th><th rowspan="2">เช้า<br>fix ER</th><th rowspan="2">รวมเวร<br>ในตาราง</th><th rowspan="2">ขอหยุด<br>(เวร)</th></tr>
    <tr>${DISP.map(s=>`<th class="sh-${s}">${SHN[s]}</th>`).join('')}${DISP.map(s=>`<th class="sh-${s} hol">${SHN[s]}</th>`).join('')}<th>ธรรมดา</th><th class="t-ref">refer</th></tr>
  </thead><tbody>${rows}
    <tr class="sum"><th class="stick dcell">รวม</th>${DISP.map(s=>`<td class="num">${tot.wd[s]}</td>`).join('')}${DISP.map(s=>`<td class="num">${tot.hd[s]}</td>`).join('')}<td class="num">${tot.reg}</td><td class="num">${tot.ref}</td><td class="num tot">${tot.total}</td><td class="num">${tot.ded}</td><td class="num tot">${tot.total+tot.ded}</td><td class="num">${tot.lv}</td></tr>
  </tbody></table></div>`+holesPanel(sc);
}

function holesPanel(sc){
  const {ctx,holes}=diagnose(sc);if(!holes.length)return '';
  const head=ctx.staff.map(st=>`<th>${esc(st.name)}</th>`).join('');
  const rows=holes.map(h=>`<tr><th class="stick dcell ${isHol(h.d)?'hol':''}"><b>${h.d}</b> <span>${TH_DOW[dow(h.d)]}</span> ${SHN[h.s]} ${h.t==='ref'?'refer':'ธรรมดา'}</th>${h.why.map(w=>`<td class="why ${w?'':'can'}">${w||'จัดได้'}</td>`).join('')}</tr>`).join('');
  return `<section class="panel" style="margin-top:18px"><h2>ทำไมยังมีเวรว่าง</h2><p class="hint">แต่ละช่องคือเหตุผลที่ระบบลงชื่อคนนั้นในเวรว่างไม่ได้ ถ้าช่องไหนเขียนว่า "จัดได้" ให้เลือกชื่อในแท็บตารางเวรได้เลย หรือกดจัดเวรใหม่</p>
  <div class="wrap"><table class="g"><thead><tr><th class="stick">เวรที่ว่าง</th>${head}</tr></thead><tbody>${rows}</tbody></table></div></section>`;
}
// ---------- export ----------
const DL=true; // บน GitHub Pages ดาวน์โหลดไฟล์ผ่านเบราว์เซอร์ได้โดยตรง
const LIBS={xlsx:'https://cdnjs.cloudflare.com/ajax/libs/xlsx/0.18.5/xlsx.full.min.js',h2c:'https://cdnjs.cloudflare.com/ajax/libs/html2canvas/1.4.1/html2canvas.min.js',pdf:'https://cdnjs.cloudflare.com/ajax/libs/jspdf/2.5.1/jspdf.umd.min.js'};
const loaded={};
function loadScript(src){return loaded[src]=loaded[src]||new Promise((ok,no)=>{const e=document.createElement('script');e.src=src;e.onload=ok;e.onerror=()=>{delete loaded[src];no(new Error('โหลดไลบรารีไม่สำเร็จ'));};document.head.appendChild(e);});}
const docTitle=()=>`ตารางปฏิบัติงานพยาบาล เดือน${TH_MONTHS[S.m]} พ.ศ. ${S.y+543}`;
const fileBase=()=>`ตารางเวรพยาบาล_${TH_MONTHS[S.m]}${S.y+543}`;
function cellCodes(sc,d,sid){const out=[];DISP.forEach(s=>['reg','ref'].forEach(t=>{if(sc[d][s][t].includes(sid))out.push({s,t,fx:s==='M'&&t==='reg'&&sc[d].fix.includes(sid)});}));return out;}
const codeText=c=>c.fx?'ER':SHC[c.s]+(c.t==='ref'?'R':'');
function posCols(){const cols=[];DISP.forEach(s=>{const nr=Math.max(+S.req.wd[s][0]||0,+S.req.hd[s][0]||0),nf=Math.max(+S.req.wd[s][1]||0,+S.req.hd[s][1]||0);
  for(let i=0;i<nr;i++)cols.push({s,t:'reg',i,label:`${SHN[s]} ธรรมดา${nr>1?' '+(i+1):''}`});for(let i=0;i<nf;i++)cols.push({s,t:'ref',i,label:`${SHN[s]} refer${nf>1?' '+(i+1):''}`});});return cols;}
async function saveFile(filename,data){
  try{
    const blob=data instanceof Blob?data:new Blob([data]);
    const url=URL.createObjectURL(blob),a=document.createElement('a');
    a.href=url;a.download=filename;document.body.appendChild(a);a.click();a.remove();
    setTimeout(()=>URL.revokeObjectURL(url),4000);toast('ดาวน์โหลดไฟล์แล้ว');
  }catch(e){toast('บันทึกไฟล์ไม่สำเร็จ');}
}
async function exportXLSX(){
  await loadScript(LIBS.xlsx);
  const sc=normalize(S.sched[ym()]),D=nDays(),{res}=stats(sc),staff=shownStaff(sc),head=[S.unit||'',docTitle()].filter(Boolean);
  const wb=XLSX.utils.book_new();
  // รายบุคคล
  const days=Array.from({length:D},(_,i)=>i+1);
  const a=[...head.map(h=>[h]),[],['เจ้าหน้าที่',...days,'OT (นับเฉลี่ย)','เช้า fix ER','รวมเวรในตาราง'],['',...days.map(d=>TH_DOW[dow(d)]+(isHol(d)?' (หยุด)':'')),'','','']];
  staff.forEach(st=>{a.push([st.name+(st.fix?' (fix ER)':''),...days.map(d=>{const c=cellCodes(sc,d,st.id);return c.length?c.map(codeText).join(' '):(lv(st.id,d).length===3?'ขอหยุด':'');}),res[st.id].total,res[st.id].fx,res[st.id].total+res[st.id].fx]);});
  a.push([],['ช = เช้า, บ = บ่าย, ด = ดึก, R = เวร refer, ER = เช้า fix ER (ไม่นับเฉลี่ย)']);
  const ws1=XLSX.utils.aoa_to_sheet(a);ws1['!cols']=[{wch:22},...days.map(()=>({wch:6})),{wch:13},{wch:11},{wch:14}];
  ws1['!merges']=head.map((_,i)=>({s:{r:i,c:0},e:{r:i,c:D+3}}));
  XLSX.utils.book_append_sheet(wb,ws1,'รายบุคคล');
  // รายวัน
  const cols=posCols();const nm=id=>{const st=S.staff.find(x=>x.id===id);return st?st.name:'';};
  const b=[...head.map(h=>[h]),[],['วันที่','วัน','ประเภทวัน',...cols.map(c=>c.label)]];
  for(let d=1;d<=D;d++)b.push([d,TH_DOW[dow(d)],isHol(d)?(fixedHol(d)||'วันหยุด'):'วันธรรมดา',...cols.map(c=>{const arr=sc[d][c.s][c.t];if(c.i>=arr.length)return '-';const v=arr[c.i];if(!v)return 'ว่าง';return nm(v)+(c.s==='M'&&c.t==='reg'&&sc[d].fix.includes(v)?' (fix ER)':'');})]);
  const ws2=XLSX.utils.aoa_to_sheet(b);ws2['!cols']=[{wch:7},{wch:5},{wch:18},...cols.map(()=>({wch:18}))];
  ws2['!merges']=head.map((_,i)=>({s:{r:i,c:0},e:{r:i,c:cols.length+2}}));
  XLSX.utils.book_append_sheet(wb,ws2,'รายวัน');
  // สรุป
  const c=[...head.map(h=>[h]),[],['เจ้าหน้าที่','วันธรรมดา','','','วันหยุด/นักขัตฤกษ์','','','ประเภทเวร','','OT (นับเฉลี่ย)','เช้า fix ER','รวมเวรในตาราง','ขอหยุด (เวร)'],['','เช้า','บ่าย','ดึก','เช้า','บ่าย','ดึก','ธรรมดา','refer','','','','']];
  const tot=new Array(12).fill(0);
  staff.forEach(st=>{const r=res[st.id];let lvn=0;for(let d=1;d<=D;d++)lvn+=lv(st.id,d).length;
    const row=[...DISP.map(s=>r.wd[s]),...DISP.map(s=>r.hd[s]),r.reg,r.ref,r.total,r.fx,r.total+r.fx,lvn];row.forEach((v,i)=>tot[i]+=v);c.push([st.name,...row]);});
  c.push(['รวม',...tot]);
  const ws3=XLSX.utils.aoa_to_sheet(c);ws3['!cols']=[{wch:22},...new Array(12).fill({wch:10})];const hr=head.length+1;
  ws3['!merges']=[...head.map((_,i)=>({s:{r:i,c:0},e:{r:i,c:12}})),{s:{r:hr,c:1},e:{r:hr,c:3}},{s:{r:hr,c:4},e:{r:hr,c:6}},{s:{r:hr,c:7},e:{r:hr,c:8}},...[0,9,10,11,12].map(k=>({s:{r:hr,c:k},e:{r:hr+1,c:k}}))];
  XLSX.utils.book_append_sheet(wb,ws3,'สรุป');
  const buf=XLSX.write(wb,{type:'array',bookType:'xlsx'});
  await saveFile(fileBase()+'.xlsx',new Blob([buf]));
}
function pdfPages(sc){
  const D=nDays(),{res}=stats(sc),staff=shownStaff(sc),cols=posCols();
  const hdr=sub=>`<div class="ph"><div>${S.unit?`<div class="pu">${esc(S.unit)}</div>`:''}<div class="pt">${docTitle()}</div></div><div class="ps">${sub}</div></div>`;
  const legend=`<div class="pl"><span class="c M">ช</span> เช้า <span class="c A">บ</span> บ่าย <span class="c N">ด</span> ดึก <span class="c A r">บ</span> ตัวแดง = เวร refer <span class="c E">ER</span> เช้า fix ER (ไม่นับเฉลี่ย) <span class="hsw"></span> วันหยุด</div>`;
  let dh='';for(let d=1;d<=D;d++)dh+=`<th class="${isHol(d)?'h':''}">${d}<br><small>${TH_DOW[dow(d)]}</small></th>`;
  const pr=staff.map(st=>{let r=`<td class="n">${esc(st.name)}</td>`;for(let d=1;d<=D;d++){const c=cellCodes(sc,d,st.id);
    r+=`<td class="${isHol(d)?'h':''}">${c.map(x=>`<span class="c ${x.fx?'E':x.s} ${x.t==='ref'?'r':''}">${x.fx?'ER':SHC[x.s]}</span>`).join('')}${!c.length&&lv(st.id,d).length===3?'<span class="o">หยุด</span>':''}</td>`;}
    return `<tr>${r}<td class="b">${res[st.id].total}</td><td>${res[st.id].fx||''}</td><td class="b">${res[st.id].total+res[st.id].fx}</td></tr>`;}).join('');
  const p1=`<div class="pp">${hdr('ตารางรายบุคคล')}<table class="pg per"><thead><tr><th class="n">เจ้าหน้าที่</th>${dh}<th>OT</th><th>ER</th><th>รวม</th></tr></thead><tbody>${pr}</tbody></table>${legend}</div>`;
  const nm=id=>{const st=S.staff.find(x=>x.id===id);return st?esc(st.name):'';};
  let dr='';for(let d=1;d<=D;d++){const h=isHol(d);dr+=`<tr class="${h?'h':''}"><td class="n">${d} ${TH_DOW[dow(d)]}${h&&fixedHol(d)?` <small>${fixedHol(d)}</small>`:''}</td>${cols.map(c=>{const arr=sc[d][c.s][c.t];if(c.i>=arr.length)return '<td class="x"></td>';const v=arr[c.i];
    return `<td class="${c.t==='ref'?'rf':''}">${v?nm(v)+(c.s==='M'&&c.t==='reg'&&sc[d].fix.includes(v)?' <span class="c E">ER</span>':''):'<span class="o">ว่าง</span>'}</td>`;}).join('')}</tr>`;}
  const p2=`<div class="pp">${hdr('ตารางรายวัน')}<table class="pg day"><thead><tr><th class="n">วันที่</th>${cols.map(c=>`<th class="t${c.s} ${c.t==='ref'?'rf':''}">${c.label}</th>`).join('')}</tr></thead><tbody>${dr}</tbody></table></div>`;
  const tot=new Array(12).fill(0);
  const sr=staff.map(st=>{const r=res[st.id];let lvn=0;for(let d=1;d<=D;d++)lvn+=lv(st.id,d).length;const row=[...DISP.map(s=>r.wd[s]),...DISP.map(s=>r.hd[s]),r.reg,r.ref,r.total,r.fx,r.total+r.fx,lvn];row.forEach((v,i)=>tot[i]+=v);
    return `<tr><td class="n">${esc(st.name)}${st.fix?' (fix ER)':''}</td>${row.map((v,i)=>`<td class="${i===8||i===10?'b':''}">${v}</td>`).join('')}</tr>`;}).join('');
  const p3=`<div class="pp">${hdr('สรุปจำนวนเวร')}<table class="pg sum"><thead><tr><th class="n" rowspan="2">เจ้าหน้าที่</th><th colspan="3">วันธรรมดา</th><th colspan="3" class="h">วันหยุด / นักขัตฤกษ์</th><th colspan="2">ประเภทเวร</th><th rowspan="2">OT<br>(นับเฉลี่ย)</th><th rowspan="2">เช้า<br>fix ER</th><th rowspan="2">รวมเวร<br>ในตาราง</th><th rowspan="2">ขอหยุด<br>(เวร)</th></tr>
    <tr>${DISP.map(s=>`<th class="t${s}">${SHN[s]}</th>`).join('')}${DISP.map(s=>`<th class="t${s} h">${SHN[s]}</th>`).join('')}<th>ธรรมดา</th><th class="rf">refer</th></tr></thead>
    <tbody>${sr}<tr class="tot"><td class="n">รวม</td>${tot.map(v=>`<td>${v}</td>`).join('')}</tr></tbody></table>
    <div class="sig"><div>ลงชื่อ ....................................................<br>(....................................................)<br>ผู้จัดตารางเวร</div><div>ลงชื่อ ....................................................<br>(....................................................)<br>ผู้อนุมัติ</div></div></div>`;
  return p1+p2+p3;
}
async function exportPDF(){
  await Promise.all([loadScript(LIBS.h2c),loadScript(LIBS.pdf)]);
  const sc=normalize(S.sched[ym()]);const box=document.createElement('div');box.className='pdfbox';box.innerHTML=pdfPages(sc);document.body.appendChild(box);
  try{
    if(document.fonts&&document.fonts.ready)await document.fonts.ready;
    const pdf=new window.jspdf.jsPDF({orientation:'landscape',unit:'mm',format:'a4'});
    const pages=box.querySelectorAll('.pp');
    for(let i=0;i<pages.length;i++){
      const c=await html2canvas(pages[i],{scale:2,backgroundColor:'#ffffff',logging:false});
      if(i)pdf.addPage();const W=297,H=210,m=8;let w=W-2*m,h=w*c.height/c.width;if(h>H-2*m){h=H-2*m;w=h*c.width/c.height;}
      pdf.addImage(c.toDataURL('image/jpeg',0.92),'JPEG',(W-w)/2,m,w,h);
    }
    await saveFile(fileBase()+'.pdf',pdf.output('blob'));
  }finally{box.remove();}
}
function tsvSchedule(){
  const sc=normalize(S.sched[ym()]),D=nDays();
  let out=['เจ้าหน้าที่',...Array.from({length:D},(_,i)=>i+1),'รวม'].join('\t')+'\n';
  const {res}=stats(sc);
  shownStaff(sc).forEach(st=>{const row=[st.name];for(let d=1;d<=D;d++){let c='';DISP.forEach(s=>['reg','ref'].forEach(t=>{if(sc[d][s][t].includes(st.id))c+=(s==='M'&&t==='reg'&&sc[d].fix.includes(st.id))?'ER':SHC[s]+(t==='ref'?'(R)':'');}));row.push(c);}row.push(res[st.id].total);out+=row.join('\t')+'\n';});
  return out;
}
function tsvSummary(){
  const sc=normalize(S.sched[ym()]),{res}=stats(sc);
  let out=['เจ้าหน้าที่','ธรรมดา-เช้า','ธรรมดา-บ่าย','ธรรมดา-ดึก','วันหยุด-เช้า','วันหยุด-บ่าย','วันหยุด-ดึก','เวรธรรมดา','เวร refer','OT (นับเฉลี่ย)','เช้า fix ER','รวมเวรในตาราง'].join('\t')+'\n';
  shownStaff(sc).forEach(st=>{const r=res[st.id];out+=[st.name,...DISP.map(s=>r.wd[s]),...DISP.map(s=>r.hd[s]),r.reg,r.ref,r.total,r.fx,r.total+r.fx].join('\t')+'\n';});
  return out;
}
async function copyText(t){
  try{await navigator.clipboard.writeText(t);toast('คัดลอกแล้ว วางใน Excel ได้เลย');return;}catch(e){}
  const old=view.querySelector('.copybox');if(old)old.remove();
  const ta=document.createElement('textarea');ta.className='copybox';ta.value=t;ta.readOnly=true;
  view.querySelector('.bar').after(ta);ta.focus();ta.select();toast('เลือกข้อความให้แล้ว กด Ctrl+C / ⌘+C เพื่อคัดลอก');
}

// events
$('#prev').onclick=()=>{S.m--;if(S.m<0){S.m=11;S.y--;}save();render();};
$('#next').onclick=()=>{S.m++;if(S.m>11){S.m=0;S.y++;}save();render();};
document.querySelector('.tabs').onclick=e=>{const b=e.target.closest('[data-tab]');if(b){tab=b.dataset.tab;render();}};
view.addEventListener('change',e=>{
  const t=e.target,ds=t.dataset;
  if(ds.req){const [k,s,i]=ds.req.split('|');S.req[k][s][+i]=Math.max(0,Math.min(9,+t.value||0));save();renderSetup();}
  else if(ds.rule){const k=ds.rule;let v=t.type==='checkbox'?t.checked:t.value;
    if(k==='maxConsec'||k==='maxPerDay')v=Math.max(0,+v||0);if(k==='nightFirst')v=v==='1';
    S.rules[k]=v;if(k==='allowCont'&&v&&+S.rules.maxPerDay<2){S.rules.maxPerDay=2;toast('ปรับเวรสูงสุดต่อวันเป็น 2 เพื่อให้ควบเวรได้');}
    save();renderSetup();}
  else if(ds.sname!==undefined){const st=S.staff.find(s=>s.id===ds.sname);if(st){st.name=t.value.trim()||st.name;save();}}
  else if(ds.unit!==undefined){S.unit=t.value.trim();save();}
  else if(t.id==='restoreFile'&&t.files&&t.files[0]){const f=t.files[0];t.value='';
    f.text().then(async txt=>{let o;try{o=JSON.parse(txt);}catch(err){toast('ไฟล์นี้ไม่ใช่ไฟล์สำรองของโปรแกรม');return;}
      if(!o||!Array.isArray(o.staff)||!o.req){toast('ไฟล์นี้ไม่ใช่ไฟล์สำรองของโปรแกรม');return;}
      if(!await askConfirm('นำเข้าไฟล์สำรอง? ข้อมูลปัจจุบันในเครื่องนี้จะถูกแทนที่ทั้งหมด','นำเข้า'))return;
      S=Object.assign(defState(),o);S.rules=Object.assign(defState().rules,o.rules||{});save();render();toast('นำเข้าข้อมูลแล้ว');});}
  else if(t.id==='staffCount'){setStaffCount(+t.value);}
  else if(ds.sfix){const st=S.staff.find(x=>x.id===ds.sfix);if(st){st.fix=t.checked;save();renderStaff();}}
  else if(ds.sded){const o=S.ded[ym()]=S.ded[ym()]||{};o[ds.sded]=t.value===''?'':Math.max(0,+t.value||0);save();renderStaff();}
  else if(ds.son){const o=S.off[ym()]=S.off[ym()]||{};if(t.checked)delete o[ds.son];else o[ds.son]=true;save();renderStaff();}
  else if(ds.sref){const st=S.staff.find(s=>s.id===ds.sref);if(st){st.refer=t.checked;save();}}
  else if(ds.smax!==undefined){const st=S.staff.find(s=>s.id===ds.smax);if(st){st.max=t.value===''?'':Math.max(0,+t.value||0);save();}}
  else if(ds.pos){const [d,s,tt,i]=ds.pos.split('|');S.sched[ym()][d][s][tt][+i]=t.value||null;save();renderSched();}
});
view.addEventListener('click',async e=>{
  const t=e.target;
  const hb=t.closest('[data-hol]');if(hb){const d=+hb.dataset.hol,o=S.hol[ym()]=S.hol[ym()]||{},nv=!isHol(d);if(nv===autoHol(d))delete o[d];else o[d]=nv;save();renderSetup();return;}
  const lc=t.closest('td.lv');if(lc){e.stopPropagation();openPop(lc);return;}
  const nom=t.closest('[data-snom]');if(nom){const [sid,sh]=nom.dataset.snom.split('|');toggleNoShift(sid,sh);return;}
  const del=t.closest('[data-sdel]');if(del){const st=S.staff.find(s=>s.id===del.dataset.sdel);if(st&&await askConfirm(`ลบ ${st.name} ออกจากรายชื่อทุกเดือน?`,'ลบออก')){S.staff=S.staff.filter(s=>s!==st);save();renderStaff();}return;}
  if(t.id==='addStaff'){const id='s'+(S.seq++);S.staff.push({id,name:'พยาบาล '+(S.staff.length+1),refer:true,max:''});save();renderStaff();
    const inp=view.querySelector(`[data-sname="${id}"]`);if(inp){inp.focus();inp.select();}return;}
  if(t.id==='allOn'){delete S.off[ym()];save();renderStaff();return;}
  if(t.id==='allOff'){const o=S.off[ym()]={};S.staff.forEach(x=>o[x.id]=true);save();renderStaff();return;}
  if(t.id==='clrLeave'){if(await askConfirm('ล้างวันขอหยุดทั้งหมดของเดือนนี้?','ล้างวันขอหยุด')){delete S.leaves[ym()];save();renderStaff();}return;}
  if(t.id==='gen'){
    if(!activeStaff().length){toast('ยังไม่มีพยาบาลที่ขึ้นเวรเดือนนี้');return;}
    if(S.sched[ym()]&&!await askConfirm('จัดเวรใหม่ทั้งเดือน? การแก้ไขเองในตารางเดิมจะหายไป','จัดเวรใหม่'))return;
    t.disabled=true;t.textContent='กำลังจัดเวร...';
    setTimeout(()=>{const sol=solve(700,1600);S.sched[ym()]=sol.sched;S.sig=S.sig||{};S.sig[ym()]=sigNow();save();renderSched();
      toast(sol.unfilled?`จัดเสร็จ ยังว่าง ${sol.unfilled} ตำแหน่ง ลองเพิ่มคนหรือผ่อนเงื่อนไข`:'จัดเวรครบทุกตำแหน่งแล้ว');},30);return;}
  const pv=t.closest('[data-pv]');if(pv){pview=pv.dataset.pv;renderSched();return;}
  if(t.id==='clrSched'){if(await askConfirm('ล้างตารางเวรของเดือนนี้?','ล้างตาราง')){delete S.sched[ym()];save();renderSched();}return;}
  if(t.id==='xlsx'||t.id==='pdf'){const lbl=t.textContent;view.querySelectorAll('.exp').forEach(b=>b.disabled=true);t.textContent='กำลังสร้างไฟล์...';
    try{await (t.id==='xlsx'?exportXLSX():exportPDF());}catch(err){toast(err&&err.message?err.message:'สร้างไฟล์ไม่สำเร็จ');}
    finally{view.querySelectorAll('.exp').forEach(b=>b.disabled=false);t.textContent=lbl;}return;}
  if(t.id==='backup'){const d=new Date();saveFile(`ตารางเวรพยาบาล_สำรอง_${d.getFullYear()+543}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}.json`,new Blob([JSON.stringify(S,null,1)],{type:'application/json'}));return;}
  if(t.id==='copy'){copyText(tsvSchedule());return;}
  if(t.id==='copySum'){copyText(tsvSummary());return;}
});
view.addEventListener('keydown',e=>{const lc=e.target.closest&&e.target.closest('td.lv');if(lc&&(e.key==='Enter'||e.key===' ')){e.preventDefault();openPop(lc);}});
pop.addEventListener('click',e=>{
  e.stopPropagation();const b=e.target.closest('[data-pl]');if(!b)return;
  const [sid,ds]=pop.dataset.cell.split('|'),d=+ds;let a=[...lv(sid,d)];const k=b.dataset.pl;
  if(k==='ALL')a=a.length===3?[]:['M','A','N'];else if(k==='CLR')a=[];else a=a.includes(k)?a.filter(x=>x!==k):[...a,k];
  setLeave(sid,d,a);
});
document.addEventListener('click',()=>{pop.hidden=true;});
document.addEventListener('keydown',e=>{if(e.key==='Escape')pop.hidden=true;});
window.addEventListener('resize',()=>{pop.hidden=true;});

load();render();
