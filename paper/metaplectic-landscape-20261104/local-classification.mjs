// Exact finite local calculations accompanying main.tex.
// Scope: all 125 quintic residue triples; all G2 quotient cosets for n=7,12.
// These calculations do not prove a global theta identity or analytic estimate.
import assert from "node:assert/strict";

const mod = (x, n) => ((x % n) + n) % n;
const gcd = (a, b) => b ? gcd(b, a % b) : a;
const supportRows = [
 [0,0,0,0],[0,0,1,0],[0,1,0,0],[0,1,3,2],
 [0,2,2,2],[0,2,3,2],[1,0,0,0],[1,0,2,1],
 [1,1,1,1],[1,1,3,2],[1,3,1,3],[1,3,2,3],
 [2,0,1,1],[2,0,2,1],[2,2,0,2],[2,2,2,3],
 [2,3,1,3],[2,3,3,4],[3,1,0,2],[3,1,1,2],
 [3,2,0,2],[3,2,3,4],[3,3,2,4],[3,3,3,4]
];
// Fourth entry: maintained model's squaredPower, not an assumed theta coefficient.
const rowMap = new Map(supportRows.map(([a,b,c,power]) =>
 [[a,b,c].join(","),power]));
assert.equal(rowMap.size,24);
let total = 0;
const isotropic = [];
for (let a=0;a<5;a++) for(let b=0;b<5;b++) for(let c=0;c<5;c++) {
 total++;
 const key=[a,b,c].join(",");
 const weights=[mod(a+b+c+3,5),mod(b+c+2,5),mod(c+1,5),0];
 const supported=new Set(weights).size===4;
 assert.equal(rowMap.has(key),supported);
 if (!supported) continue;
 const self=2*a*a+6*a*b+8*a*c+6*b*b+16*b*c+12*c*c;
 if (self%5!==0) continue;
 const power=rowMap.get(key),height=a+2*b+3*c;
 isotropic.push({v:[a,b,c],power,height,defect:height-power});
}
assert.equal(total,125);
assert.deepEqual(isotropic.map(o=>o.v),
 [[0,0,0],[1,1,1],[2,2,2],[3,3,3]]);
// Bilinearity now gives E(mv,nv)=-25mn and B(mv,nv)=50mn.
const v=[1,1,1];
const E=(u,w)=>(u[0]+u[1]+u[2])*(w[1]+2*w[2])
 +(u[1]+u[2])*w[2]
 -(u[0]+2*u[1]+3*u[2])*(w[0]+2*w[1]+3*w[2]);
assert.equal(E(v,v),-25);
assert.deepEqual([mod(8-1,5),mod(1+1+1,5),1],[2,3,1]);

function g2Orbits(n) {
 const m=n/gcd(n,3),seen=new Set(),orbits=[];
 for(let a=0;a<n;a++) for(let b=0;b<m;b++) {
  const key=[a,b].join(",");
  if(seen.has(key)) continue;
  const queue=[[a,b]],orbit=new Set([key]);
  for(let i=0;i<queue.length;i++) {
   const[x,y]=queue[i];
   for(const[u,w] of [[mod(1-x+3*y,n),y],[x,mod(1+x-y,m)]]) {
    const k=[u,w].join(",");
    if(!orbit.has(k)) {orbit.add(k);queue.push([u,w]);}
   }
  }
  for(const k of orbit) seen.add(k);
  orbits.push({representative:[a,b],size:orbit.size});
 }
 assert.equal(seen.size,n*m);
 const free=orbits.filter(o=>o.size===12).length;
 assert.equal(free,1);
 return {n,rootPeriods:[n,m],quotientSize:n*m,orbits,freeOrbits:free};
}
const result={
 scope:"Exact finite local algebra; no analytic extrapolation",
 quintic_isotropic_supported_states:isotropic,
 quintic_torus_cocycle_on_diagonal:-25,
 quintic_pairing_on_diagonal:50,
 g2:[g2Orbits(7),g2Orbits(12)]
};
console.log(JSON.stringify(result,null,2));
