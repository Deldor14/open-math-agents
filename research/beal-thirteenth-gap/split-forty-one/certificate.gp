\\ PARI/GP 2.19.1. Arithmetic in the real sextic field and at its prime over 41.
F=y^6+y^5-5*y^4-4*y^3+6*y^2+3*y-1;
p=41;
classpart()={my(g=lift(chinese(Mod(-1,13),Mod(1,p))),A=subcyclopclgp([13*p,[g]],p,1));print("class data ",A);if(A[2][1] || A[3][1],error("nonzero p-part"))};
entry()={my(Z=Mod(Mod(1,p^2)*x,Mod(1,p^2)*polcyclo(13)),n=p^12-1,A=select(t->(t+(1-t)*Z)^n==1,[0..p^2-1]),B=lift((1-Z)^n));if(A!=[0,1] || poldegree(B)<1,error("entry"));print("normalized residues ",A,"; infinity nonscalar coefficient ",pollead(B))};
\\ Residue field and smooth points chosen by specifying the 41st roots of their ordinates.
r=ffgen(Mod(1,p)*F,'r);U=(r+1)*(r+2);Y0=2*r+3;W=6+r-2*r^2;d=U^(p^5);
g=(p-1)/2;zs=concat([2..g],[r]);rs=apply(z->(z^2-1)/(4*d),zs);ys=apply(z->z^p,zs);
M=matrix(g,g,j,i,rs[i]^(j-1)/ys[i]);b=matsolve(M,Col(vector(g,j,j*W/Y0)));
\\ Lift into (O_H/1681)[x]/Phi_41(1+x); x represents xi-1.
base=Mod(Mod(1,p^2)*y,Mod(1,p^2)*F);unit=(base+1)*(base+2);
liftk(a)={my(P=liftint((a+r-r).pol));subst(P,variable(r.pol),base)};
pii=Mod(x,subst(polcyclo(p),x,1+x)*base^0);
ordlift(X,z)={my(yv=liftk(z)*pii^0,target=1+4*unit*X^p);for(i=1,7,yv=(yv+target*yv^((p^6-1)*p^2-1))/2);if(yv^2!=target,error("Newton lift"));yv};
check()={my(Km=pii^0);for(i=1,g,my(X=liftk(rs[i])*pii^0,Y=ordlift(X,ys[i]),Z=ordlift(X+pii*liftk(b[i]),ys[i]));Km*=(1+Z)*(1+Y)^((p^6-1)*p^2-1));my(coeff=lift(Km-1),k0=liftint(lift(polcoef(coeff,0))),k1=liftint(lift(polcoef(coeff,1))));if(Mod(1,p^2)*k0!=0 || Mod(1,p)*k1!=0,error("low coefficients"));for(i=2,p-2,if(Mod(1,p)*liftint(lift(polcoef(coeff,i)))!=0,error("intermediate coefficient")));my(L=subst(-k1/p,y,r),closed=W*(U/Y0^3)^(p^5));print("twenty-section trace ",trace(L),"; closed trace ",trace(closed),"; closed residue ",closed);if(lift(trace(L))!=31 || trace(closed)!=trace(L),error("trace"));};
run()={if(!polisirreducible(Mod(1,p)*F) || polresultant(F,(y+1)*(y+2))^2!=1 || polresultant(F,2*y+3)^2!=1,error("field or unit"));classpart();entry();check()};
iferr(run(),exc,print(exc);quit(1));
quit
