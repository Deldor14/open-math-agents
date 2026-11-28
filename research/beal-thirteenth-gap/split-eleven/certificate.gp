\\ PARI/GP 2.19.1. Arithmetic in the real sextic field and at its prime over 11.
F=y^6+y^5-5*y^4-4*y^3+6*y^2+3*y-1;
classpart()={my(A=subcyclopclgp([143,[12]],11,1));print("class data ",A);if(A[2][1] || A[3][1],error("nonzero 11-part"))};
entry()={my(Z=Mod(Mod(1,121)*x,Mod(1,121)*polcyclo(13)),n=11^12-1,A=select(t->(t+(1-t)*Z)^n==1,[0..120]),B=lift((1-Z)^n));if(A!=[0,1] || poldegree(B)<1,error("entry"));print("normalized residues ",A,"; infinity test ",B)};
\\ Residue field and smooth points chosen by specifying the 11th roots of their ordinates.
r=ffgen(Mod(1,11)*F,'r);U=(r+1)*(r+2);Y0=2*r+3;W=6+r-2*r^2;d=U^(11^5);
zs=[2,3,4,5,r];rs=apply(z->(z^2-1)/(4*d),zs);ys=apply(z->z^11,zs);
M=matrix(5,5,j,i,rs[i]^(j-1)/ys[i]);b=matsolve(M,Col(vector(5,j,j*W/Y0)));
\\ Lift into (O_H/121)[x]/Phi_11(1+x); x represents xi-1.
base=Mod(Mod(1,121)*y,Mod(1,121)*F);unit=(base+1)*(base+2);
liftk(a)={my(P=liftint((a+r-r).pol));subst(P,variable(r.pol),base)};
pii=Mod(x,subst(polcyclo(11),x,1+x)*base^0);
ordlift(X,z)={my(yv=liftk(z)*pii^0,target=1+4*unit*X^11);for(i=1,5,yv=(yv+target*yv^((11^6-1)*121-1))/2);if(yv^2!=target,error("Newton lift"));yv};
check()={my(Km=pii^0);for(i=1,5,my(X=liftk(rs[i])*pii^0,Y=ordlift(X,ys[i]),Z=ordlift(X+pii*liftk(b[i]),ys[i]));Km*=(1+Z)*(1+Y)^((11^6-1)*121-1));my(coeff=lift(Km-1),k0=liftint(lift(polcoef(coeff,0))),k1=liftint(lift(polcoef(coeff,1))));if(Mod(1,121)*k0!=0 || Mod(1,11)*k1!=0,error("low coefficients"));for(i=2,9,if(Mod(1,11)*liftint(lift(polcoef(coeff,i)))!=0,error("intermediate coefficient")));my(L=subst(-k1/11,y,r),closed=W*(U/Y0^3)^(11^5));print("five-section trace ",trace(L),"; closed trace ",trace(closed),"; closed residue ",closed);if(lift(trace(L))!=5 || trace(closed)!=trace(L),error("trace"));};
run()={if(!polisirreducible(Mod(1,11)*F) || polresultant(F,(y+1)*(y+2))^2!=1 || polresultant(F,2*y+3)^2!=1,error("field or unit"));classpart();entry();check()};
iferr(run(),exc,print(exc);quit(1));
quit
