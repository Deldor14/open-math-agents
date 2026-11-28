\\ Independent finite checks of cofactor lengths and nonprimitive valuations.
{my(rows=0,checks=0,moduli=[11,13,17,19,23,29,31,37,41,43]);
for(n=11,2500,if(gcd(n,210)!=1,next);
  my(t=omega(n),j=2^(t-1),phi=polcyclo(n),f=(x^n-1)\phi,cap=2^j*(n+1)^(j-1));
  if(f*phi!=x^n-1 || vecsum(apply(abs,Vec(f)))>cap,error("length at ",n));
  if(29^eulerphi(n)<=(3*n*cap)^6,error("size at ",n));
  rows++;
  foreach(moduli,r,
    if(n%r,next);
    for(k=1,r-1,
      my(a=znorder(Mod(k,r)));
      if(n%a==0 && a<n,
        if(subst(phi,x,Mod(k,r^2))==0,error("valuation at ",[n,r,k]));
        checks++))
  )
);print(rows," exact polynomial lengths; ",checks," nonprimitive valuation checks")}
