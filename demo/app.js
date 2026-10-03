/* Geometry is a view of Lean's captured values, never a substitute simulation. */
const NS='http://www.w3.org/2000/svg', $=id=>document.getElementById(id);
const colors={gray:'#777',blue:'#58c4dd',green:'#83c167',yellow:'#ffff77',orange:'#f5ae67'};
function node(parent,tag,attrs={},value) {const e=document.createElementNS(NS,tag);for(const [k,v] of Object.entries(attrs))e.setAttribute(k,v);if(value!==undefined)e.textContent=value;parent.append(e);return e;}
const txt=(p,x,y,value,cls='')=>node(p,'text',{x,y,class:cls},value);
const line=(p,x1,y1,x2,y2,color,width=1,extra={})=>node(p,'line',{x1,y1,x2,y2,stroke:color,'stroke-width':width,...extra});
const speed=v=>Math.hypot(v.x,v.y)/65536;
function movement(s) {
 const g=$('movement');g.replaceChildren();
 txt(g,24,26,'Friction', 'dim');
 const f=s.movement.friction;
 const before=f?.before||s.movement.live, after=f?.after||s.movement.live;
 const scale=83/Math.max(Math.hypot(before.x,before.y),Math.hypot(after.x,after.y),1);
 line(g,57,132,253,132,'#252525');line(g,155,42,155,222,'#252525');
 node(g,'circle',{cx:155,cy:132,r:83,fill:'none',stroke:'#171717'});
 const bx=155+before.x*scale,by=132-before.y*scale,ax=155+after.x*scale,ay=132-after.y*scale;
 if(before.x||before.y)line(g,155,132,bx,by,colors.gray,2,{'marker-end':'url(#arrowGray)'});
 if(after.x||after.y)line(g,155,132,ax,ay,colors.green,3,{'marker-end':'url(#arrowGreen)'});
 node(g,'circle',{cx:155,cy:132,r:2,fill:'#888'});
 if(f) {txt(g,bx+12,by-10,'v','math dim');txt(g,ax+12,ay+23,'F(v)','math green');}
 txt(g,32,251,'‖F(v)‖² ≤ ‖v‖²','math green');
 txt(g,32,278,f?`${after.squared} ≤ ${before.squared}`:'v = 0 · no friction call','code');
 txt(g,32,302,`|v| = ${speed(s.movement.live).toFixed(3)} units/tic`,'tiny');
 txt(g,32,328,'friction_speed_squared body cmd','code');
 if(s.flying||s.health===0)txt(g,24,52,'last player sample','tiny');
}
function aim(s) {
 const g=$('aim');g.replaceChildren();
 const a=s.aim,w=a?.window,shot=s.weapon.lastFire;
 txt(g,24,26,'Autoaim','dim');
 txt(g,1020,26,shot?`last ${shot.gun} shot · tic ${shot.tic}`:'fire toward an actor', 'tiny').setAttribute('text-anchor','end');
 if(!w) {
  line(g,45,166,640,166,'#444',1,{'stroke-dasharray':'4 7'});
  node(g,'circle',{cx:45,cy:166,r:4,fill:'#aaa'});
  txt(g,45,199,'muzzle','tiny');txt(g,195,140,a?'No autoaim target selected':'Waiting for a shot','dim');
  txt(g,700,110,'b ≤ center ≤ t','math blue');
  txt(g,700,149,'lower ≤ rise ≤ upper','math');
  txt(g,700,207,'autoaim_trajectory_inside','code');
  txt(g,700,231,'bottom top distance','code');
  txt(g,45,304,'The geometric proof needs a nonempty clipped window.','tiny');
  txt(g,45,328,'0 ≤ distance ≤ 1024 map units','tiny');return;
 }
 const d=w.distance/65536,z0=w.shootZ/65536,lo=w.bottom/65536,hi=w.top/65536,slope=a.slope/65536;
 const valid=w.bottom>=-40960&&w.bottom<=w.top&&w.top<=40960&&w.distance>=0&&w.distance<=67108864;
 if(!valid){txt(g,65,165,'Observed window lies outside this theorem’s bounds.','dim');return;}
 const targetLow=w.targetZ/65536-z0,targetHigh=(w.targetZ+w.targetHeight)/65536-z0;
 const ymin=Math.min(-8,targetLow,lo*d),ymax=Math.max(8,targetHigh,hi*d),pad=Math.max(8,(ymax-ymin)*.2);
 const X=v=>45+535*v/Math.max(d,1),Y=v=>258-202*(v-ymin+pad)/(ymax-ymin+2*pad);
 const ground=Y(0),profile=node(g,'g',{'clip-path':'url(#profileClip)'});
 line(profile,30,ground,653,ground,'#333',1,{'stroke-dasharray':'3 7'});
 node(profile,'polygon',{points:`${X(0)},${ground} ${X(d)},${Y(lo*d)} ${X(d)},${Y(hi*d)}`,fill:colors.blue,'fill-opacity':'.11'});
 for(const p of w.portals||[]) {
  const x=X(p.distance/65536),b=Y(p.bottom/65536-z0),t=Y(p.top/65536-z0);
  line(profile,x,44,x,Math.min(266,t),'#555',4);line(profile,x,Math.max(44,b),x,266,'#555',4);
  line(profile,x-6,t,x+6,t,'#999');line(profile,x-6,b,x+6,b,'#999');
 }
 line(profile,X(0),ground,X(d),Y(lo*d),colors.blue,1.3);
 line(profile,X(0),ground,X(d),Y(hi*d),colors.blue,1.3);
 line(profile,X(d),Y(targetLow),X(d),Y(targetHigh),colors.orange,7);
 line(profile,X(d),Y(lo*d),X(d),Y(hi*d),colors.blue,3);
 line(profile,X(0),ground,X(d),Y(slope*d),colors.yellow,2);
 node(profile,'circle',{cx:X(0),cy:ground,r:4,fill:'#ddd'});
 node(profile,'circle',{cx:X(d),cy:Y(slope*d),r:4,fill:colors.yellow});
 txt(g,45,286,'muzzle','tiny');txt(g,580,286,`target ${w.target}`,'tiny').setAttribute('text-anchor','middle');
 txt(g,45,55,`vertical profile · ${(w.distance/65536).toFixed(1)} units`,'tiny');
 txt(g,700,67,'s = trunc((b + t) / 2)','yellow');
 txt(g,600,Y(hi*d)+5,'t','math blue');txt(g,600,Y(lo*d)+5,'b','math blue');
 txt(g,700,110,`${w.bottom} ≤ ${a.slope} ≤ ${w.top}`,'math blue');
 const lower=Math.floor(w.bottom*w.distance/65536),rise=Math.floor(a.slope*w.distance/65536),upper=Math.floor(w.top*w.distance/65536);
 txt(g,700,147,`${lower} ≤ ${rise} ≤ ${upper}`,'code');
 txt(g,700,171,'vertical rise · exact 16.16','tiny');
 txt(g,700,284,'autoaim_trajectory_inside','code');
 txt(g,700,308,'bottom top distance','code');
 txt(g,45,328,'Every distance 0…1024; relative rise, not a hit guarantee.','tiny');
 // Horizontal direction inset uses the actual, unexaggerated binary angles.
 const ox=992,oy=253,R=61;
 const ray=(raw,color,width=1)=>{const signed=((raw-a.facing+2147483648)>>>0)-2147483648;const t=signed/4294967296*Math.PI*2;line(g,ox,oy,ox+Math.sin(t)*R,oy-Math.cos(t)*R,color,width);};
 ray(a.facing,'#666');ray((a.facing+a.offset)>>>0,colors.blue,2);
 for(const angle of a.pelletAngles)ray(angle,colors.yellow,1);
 node(g,'circle',{cx:ox,cy:oy,r:3,fill:'#ddd'});
 txt(g,969,232,'yaw','tiny').setAttribute('text-anchor','end');
 txt(g,700,213,a.offset?'side probe ≠ fired yaw':'center probe','tiny');
 txt(g,700,237,'pellet yaw in yellow','tiny');
}
let inFlight=false;
function status(message,disconnected=false){$('status').textContent=message;document.body.classList.toggle('disconnected',disconnected);}
async function poll(){
 if(inFlight)return;inFlight=true;
 try{
  const response=await fetch('/state',{cache:'no-store',signal:AbortSignal.timeout(1500)});
  if(!response.ok)throw Error('No telemetry');
  const {state:s,age,recorded}=await response.json();
  if(!s)status('waiting for the viewer',true);
  else if(s.status==='stopped')status('viewer stopped · last observed values',true);
  else if(s.schema!==1||typeof s.source!=='string')status('restart the viewer to update telemetry',true);
  else{movement(s);aim(s);$('proof').textContent=s.source;status(recorded?`recorded engine snapshot · tic ${s.tic}`:age>2?'telemetry paused · last observed values':`tic ${s.tic} · theorems checked in Lean, values observed live`,!recorded&&age>2);}
 }catch{status('disconnected · last observed values',true);}finally{inFlight=false;}
}
poll();setInterval(poll,100);
