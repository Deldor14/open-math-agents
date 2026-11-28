\\ Run in this directory using PARI/GP. No class-group algorithm is needed.
loc_at2(N,q2,B,t,z)={my(v=idealval(N,z,q2),w=ideallog(N,z/t^v,B),bits=v%2);for(i=1,#w,if(B.cyc[i]%2==0,bits=2*bits+w[i]%2));return(bits)};
loc_at13(N,s13,rho,R13,z)={my(bits=0);for(i=1,#s13,my(v=idealval(N,z,s13[i]),a=nfmodpr(N,z/(rho-4)^v,R13[i]));bits=4*bits+2*(v%2)+(a^((13^s13[i].f-1)/2)!=1));return(bits)};
localStep(r,t,j,i)={
  if(j%2,return(1+r^i*t^j));
  if(j==22 && i==2,return(1+t^22));
  return((1+r^i*t^(j/2))^2);
};
filtered(N,pr,t,modulus,red,st,tab,z)={
  my(v=idealval(N,z,pr),a=nfbasistoalg(N,nfeltreduce(N,(z/t^v)^7,modulus)),bits=v%2);
  for(j=1,22,my(b=nfmodpr(N,(a-1)/t^j,red),index=1);
    while(index<=8 && tab[j,index]!=b,index++);
    if(index>8,error("missing leading coefficient"));
    a=nfbasistoalg(N,nfeltreduce(N,a*st[j,index],modulus));
    if(j%2,bits=8*bits+index-1,if(j==22,bits=2*bits+bittest(index-1,2))));
  if(a!=1 && idealval(N,a-1,pr)<23,error("insufficient depth"));
  return(bits);
};
verify(alternative)={
  my(f=y^3+y^2-4*y+1,K=nfinit(f),r=Mod(y,f),s=r^2-r+1,c=4^10*s^11/r^2);
  my(P=x^33+2*x^22-16*x^11+8,N=nfinit(P),t=Mod(x,P),rho=t^11/2);
  my(rootc=-4*(rho^2-rho+1)/t^2, E=read("elements.json"));
  my(U=apply(e->Mod(Polrev(e[2]),P)/e[1],E), q2=idealprimedec(N,2)[1]);
  my(k2=idealprimedec(K,2)[1],k13=idealprimedec(K,13)[1],s13=idealprimedec(N,13));
  my(S=concat([idealprimedec(N,2),idealprimedec(N,11),s13]));
  my(B=idealstar(N,idealpow(N,q2,23),2),R13=apply(v->nfmodprinit(N,v),s13));
  my(emb=z->subst(lift(z),y,rho),rel=z->Mod(polresultant(x^11-2*y,lift(z),x),f));
  my(at2=z->loc_at2(N,q2,B,t,z));
  if(alternative,
    my(modulus=idealpow(N,q2,23),red=nfmodprinit(N,q2));
    my(st=matrix(22,8,j,b,prod(i=0,2,if(bittest(b-1,i),localStep(rho,t,j,i),1))));
    my(tab=matrix(22,8,j,b,nfmodpr(N,(st[j,b]-1)/t^j,red)));
    for(j=1,22,if(#Set(Vec(tab[j,]))!=8,error("filtration basis")));
    at2=z->filtered(N,q2,t,modulus,red,st,tab,z));
  my(at13=z->loc_at13(N,s13,rho,R13,z));
  my(both=z->16*at2(z)+at13(z),rank=V->matrank(Mod(1,2)*matrix(44,#V,i,j,bittest(V[j],i-1))));
  if(N.sign!=[3,15] || N.disc!=-(2^30*11^33*13^22) || rootc^11!=-emb(c),error("field"));
  if(apply(v->[v.e,v.f],S)!=[[11,3],[11,3],[3,1],[3,10]],error("bad primes"));
  if(#U!=22,error("unit count"));
  for(i=1,#U,if(denominator(nfalgtobasis(N,U[i]))!=1 || nfeltnorm(N,U[i])!=E[i][3],error("element ",i));if(i<=18 && abs(E[i][3])!=1,error("ordinary unit")));
  for(i=1,#S,if(idealhnf(N,U[18+i])!=idealhnf(N,S[i]),error("principal bad prime ",i)));
  my(G=apply(z->z*emb(rel(z)),U),g2=apply(at2,G),g=apply(both,G));
  if(rank(g2)!=16,error("dyadic injection"));
  my(w2=at2(4*emb(s)*(1+2*rho)-rootc));
  if(rank(concat(g2,[w2]))!=17,error("valuation-one obstruction"));
  my(xs=[1,4,12,4*r,4*r+8,8*r+4,12*r,3*r+3,r^2,4*r^2,4*r^2+8,4*r^2+4*r+4,4*r^2+4*r+12,4*r^2+12*r+4,8*r^2+4]);
  for(i=1,#xs,if(!nfislocalpower(K,k2,xs[i]^11+c,2),error("dyadic point ",i)));
  if(idealval(K,4*s,k13)!=1 || idealval(K,1+1/(4*r^2),k13)!=1,error("13-adic scaling"));
  if(znorder(Mod(13,11))!=10,error("residual factors at 13"));
  my(l2=apply(z->16*at2(emb(z)-rootc),xs),l13=at13(subst(polcyclo(11),x,-1/t^2)),lm=concat(l2,[l13]));
  if(rank(l2)!=15 || !l13 || rank(concat(g,lm))!=29,error("Selmer ranks"));
  my(sets=[[6,7,13,16],[4,5,6,7,8,9,12,14,15,16,17],[4,6,10,13,14,15,16,17,21]]);
  my(sel=apply(v->prod(i=1,#v,G[v[i]]),sets), bits=apply(at2,sel));
  if(rank(bits)!=3 || rank(concat(lm,apply(both,sel)))!=16,error("Selmer basis"));
  if(both(emb(4*s)-rootc)!=both(sel[3]),error("known class"));
  my(aa=r^2/(1+4*r^2), base=[1,1+r,1+r^2,1+r+r^2], tiny=List());
  for(j=1,4,for(i=0,2,my(a=base[j],h=r^i);
    if(!nfislocalpower(K,k2,1+4*aa*(a^11-1),2),error("missing basepoint"));
    if(!nfislocalpower(K,k2,1+4*aa*((a+2*h)^11-1),2),error("missing neighbor"));
    listput(tiny,at2((1+t^2*emb(a+2*h))/(1+t^2*emb(a))))));
  for(i=0,2,listput(tiny,at2(emb(s/(aa*r^(2*i)))-rootc)));
  if(rank(Vec(tiny))!=15,error("tiny-integral basis"));
  my(bm=V->Mod(1,2)*matrix(44,#V,i,j,bittest(V[j],i-1)));
  my(coeff=matinverseimage(bm(Vec(tiny)),bm(bits)));
  my(words=vector(3,j,sum(i=1,15,2^(i-1)*lift(coeff[i,j]))));
  if(words!=[8336,29771,9056],error("tiny basis coordinates"));
  print("Selmer coefficients in tiny-integral basis ",words);
  my(ord=read("principals.json"));
  if(apply(a->a[1],ord)!=[5,1607,1871],error("auxiliary rational primes"));
  for(i=1,#ord,my(q=ord[i][1],prs=idealprimedec(N,q,1),els=apply(e->Mod(Polrev(e[2]),P)/e[1],ord[i][2]));
    if(#prs!=[3,11,11][i] || Set(apply(u->idealhnf(N,u),prs))!=Set(apply(u->idealhnf(N,u),els)),error("auxiliary principals ",q)));
  print("bad principal ideals 4; auxiliary degree-one principal ideals 3+11+11");
  print("dyadic S-unit rank 16; adjoining the valuation-one candidate gives 17");
  print("local Kummer dimensions 15,1; combined rank 29; supported Selmer dimension 3");
}
iferr(verify(0);verify(1),E,print(E);quit(1));
quit
