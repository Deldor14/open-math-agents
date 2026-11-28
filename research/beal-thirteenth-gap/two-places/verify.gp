\\ PARI/GP 2.19.1. Test both completions of the real sextic field.
F=y^6+y^5-5*y^4-4*y^3+6*y^2+3*y-1;
classcheck(p)={my(h=lift(chinese(Mod(-1,13),Mod(1,p))),A=subcyclopclgp([13*p,[h]],p,1));print("conductor ",13*p," involution ",h," class data ",A);if(A[2][1] || A[3][1],error("class group"))};
entry(p)={my(Z=Mod(Mod(1,p^2)*x,Mod(1,p^2)*polcyclo(13)),n=p^12-1,A=select(t->(t+(1-t)*Z)^n==1,[0..p^2-1]));if(A!=[0,1] || poldegree(lift((1-Z)^n))<1,error("entry"));print("finite chart ",A,"; infinity nonscalar")};
represent(a,r,base)=subst(liftint((a+r-r).pol),variable(r.pol),base);
ylift(X,z,r,base,pii,p)={my(u=(base+1)*(base+2),yv=represent(z,r,base)*pii^0,target=1+4*u*X^p);for(i=1,6,yv=(yv+target*yv^((p^3-1)*p^2-1))/2);if(yv^2!=target,error("Newton"));yv};
place(p,phi)={
  my(g=(p-1)/2,r=ffgen(lift(phi)*Mod(1,p),'r),U=(r+1)*(r+2),Y0=2*r+3,W=6+r-2*r^2,d=U^(p^2));
  my(zs=concat([2..g],[r]),rs=apply(z->(z^2-1)/(4*d),zs),ys=apply(z->z^p,zs));
  my(mat=matrix(g,g,j,i,rs[i]^(j-1)/ys[i]),b=matsolve(mat,Col(vector(g,j,j*W/Y0))));
  my(base=Mod(Mod(1,p^2)*y,phi),pii=Mod(x,subst(polcyclo(p),x,1+x)*base^0),km=pii^0);
  for(i=1,g,my(X=represent(rs[i],r,base)*pii^0,Y=ylift(X,ys[i],r,base,pii,p),Z=ylift(X+pii*represent(b[i],r,base),ys[i],r,base,pii,p));km*=(1+Z)*(1+Y)^((p^3-1)*p^2-1));
  my(coeff=lift(km-1),k0=liftint(lift(polcoef(coeff,0))),k1=liftint(lift(polcoef(coeff,1))));
  if(Mod(1,p^2)*k0!=0 || Mod(1,p)*k1!=0,error("low terms"));
  for(i=2,p-2,if(Mod(1,p)*liftint(lift(polcoef(coeff,i)))!=0,error("middle terms")));
  my(L=subst(-k1/p,y,r),closed=W*(U/Y0^3)^(p^2),N=polresultant(phi,(y+1)*(y+2)),fermat=lift(N^(p-1)-1)/p);
  if(trace(closed)!=trace(L),error("traces disagree"));print("cubic ",lift(phi)," norm ",lift(N)," quotient ",fermat," boundary ",lift(trace(L)));[fermat,lift(trace(L))]
};
check(p)={classcheck(p);entry(p);my(ff=factorpadic(F,p,3));if(matsize(ff)[1]!=2,error("local degree"));my(ans=vector(2,i,place(p,liftall(ff[i,1])*Mod(1,p^2))));if(ans[1][1]==0 || (ans[1][1]+ans[2][1])%p || (ans[1][2]==0 && ans[2][2]==0),error("synchronization or boundary"))};
iferr(check(17);check(23),err,print(err);quit(1));
quit
