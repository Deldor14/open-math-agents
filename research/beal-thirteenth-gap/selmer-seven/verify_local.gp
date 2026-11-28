\\ Run with check_local.py as described in the README.
\\ All number-field operations use nfinit. The certificate needs no class group.
f=y^3+y^2-4*y+1; K=nfinit(f); r=Mod(y,f); s=r^2-r+1;
P=x^21+2*x^14-16*x^7+8; F=nfinit(P); t=Mod(x,P); rho=t^7/2;
c0=4^6*s^7/r^2; rootc=-4*(rho^2-rho+1)/t^2;
emb(z)=subst(lift(z),y,rho);
rel(z)=Mod(polresultant(x^7-2*y,lift(z),x),f);
ck(c,msg)=if(!c,error(msg));
ck(rootc^7==-emb(c0),"wrong root");
k2=idealprimedec(K,2)[1]; f2=idealprimedec(F,2)[1];
k13=idealprimedec(K,13)[1]; f13=idealprimedec(F,13);
ck(F.sign==[3,9] && F.disc==-2^18*7^21*13^14,"field data");
ck(idealval(K,4*s,k13)==1 && idealval(K,1+1/(4*r^2),k13)==1,"13-adic scaling");
bid=idealstar(F,idealpow(F,f2,15),2);
loc2(z)={
  my(v=idealval(F,z,f2), logs=ideallog(F,z/t^v,bid), mask=v%2);
  for(i=1,#logs, if(bid.cyc[i]%2==0, mask=2*mask+logs[i]%2));
  return(mask);
};
maps=apply(z->nfmodprinit(F,z),f13);
loc13(z)={
  my(mask=0);
  for(i=1,#f13,
    my(v=idealval(F,z,f13[i]), h=nfmodpr(F,z/(rho-4)^v,maps[i]), q=13^f13[i].f);
    mask=4*mask+2*(v%2)+(h^((q-1)/2)!=1));
  return(mask);
};
both(z)=256*loc2(z)+loc13(z);
rk(V)=matrank(Mod(1,2)*matrix(32,#V,i,j,bittest(V[j],i-1)));
E=read("elements.json");
g=vector(#E,i,Mod(Polrev(E[i][2]),P)/E[i][1]);
V=vector(#g,i,g[i]*emb(rel(g[i])));
for(i=1,#g,ck(rel(V[i])==rel(g[i])^8,"norm projection"));
G=apply(both,V);
\\ Nine x-coordinates of actual points above the dyadic completion.
xx=[1,4,12,4*r,4*(1+r),4*(2+r),4*(3+r),4*(1+2*r),12*r];
for(i=1,#xx,ck(nfislocalpower(K,k2,xx[i]^7+c0,2),"missing dyadic square"));
L2=apply(z->256*loc2(emb(z)-rootc),xx);
\\ Traces of points over the unramified quadratic extension at 13.
cc=[3,5,6]; L13=vector(3);
for(i=1,3,my(h=x^2+cc[i]*x+1);ck(polisirreducible(Mod(1,13)*h) && (Mod(1,13)*(x^7-1))%(Mod(1,13)*h)==0,"wrong quadratic factor");L13[i]=loc13(subst(h,x,-1/t^2)));
L=concat(L2,L13);
ck(rk(L2)==9 && rk(L13)==3 && rk(L)==12,"local ranks");
ck(rk(G)==12 && rk(concat(G,L))==23,"global/local ranks");
\\ The known point has an S-unit class, independently of the class number.
d5=(x^20-x^19+x^18-x^17+x^16-x^14+2*x^13-2*x^12+2*x^11-2*x^10+4*x^9-2*x^8-2*x^7-16*x^6+12*x^5-12*x^4+16*x^3-16*x^2+4*x+8)/4;
d5=Mod(d5,P); u0=(rho^2-rho+1)*(t^2+1)/d5^2;
ck(vecprod(apply(denominator,nfalgtobasis(F,u0)))==1 && abs(nfeltnorm(F,u0))==13^8,"known S-unit");
y0=2^6*s^4*(r^2+r-5);
ck(y0^2==(4*s)^7+c0 && emb(4*s)-rootc==u0*(2*d5/t)^2,"known divisor");
w=both(u0);
ck(w!=0 && rk(concat(L,[w]))==12 && rk(concat(G,[w]))==12,"known class");
\\ Recompute local square classes using the unit filtration at the dyadic place.
mod15=idealpow(F,f2,15); res2=nfmodprinit(F,f2);
red15(z)=nfbasistoalg(F,nfeltreduce(F,z,mod15));
genstep(j,i)={if(j%2,return(1+rho^i*t^j));if(j==14 && i==2,return(1+t^14));return((1+rho^i*t^(j/2))^2)};
steps=matrix(14,8,j,b,prod(i=0,2,if(bittest(b-1,i),genstep(j,i),1)));
leadtable=matrix(14,8,j,b,nfmodpr(F,(steps[j,b]-1)/t^j,res2));
for(j=1,14,for(b=1,8,for(c=1,b-1,ck(leadtable[j,b]!=leadtable[j,c],"filtration basis"))));
filtered2(z)={
  my(v=idealval(F,z,f2), w=red15((z/t^v)^7), mask=v%2);
  for(j=1,14,
    my(h=nfmodpr(F,(w-1)/t^j,res2), k=1);
    while(leadtable[j,k]!=h, k++);
    w=red15(w*steps[j,k]);
    if(j%2, mask=8*mask+k-1, if(j==14, mask=2*mask+bittest(k-1,2))));
  ck(w==1 || idealval(F,w-1,f2)>=15,"dyadic precision");
  return(mask);
};
alt13(z)={my(mask=0);for(i=1,#f13,my(v=idealval(F,z,f13[i]));mask=4*mask+2*(v%2)+!nfislocalpower(F,f13[i],z/(rho-4)^v,2));return(mask)};
ha(z)=256*filtered2(z)+alt13(z);
rk2(v)=matrank(Mod(1,2)*matrix(40,#v,i,j,bittest(v[j],i-1)));
Galt=apply(ha,V);
La2=apply(z->256*filtered2(emb(z)-rootc),xx);
La13=vector(3,i,alt13(subst(x^2+cc[i]*x+1,x,-1/t^2)));
La=concat(La2,La13);
ck(rk2(La2)==9 && rk2(La13)==3 && rk2(Galt)==12 && rk2(concat(Galt,La))==23,"independent character ranks");
print("dyadic rank 9; rank at 13 is 3; norm-kernel image 12; combined rank 23.");
print("The unit-supported 2-Selmer subspace has dimension 1.");
