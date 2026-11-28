\\ Independent tangent computation using rational Cantor composition.
monicpoly(g)=g/pollead(g);
reducepair(u,v,f)={
  while(poldegree(u)>3, u=monicpoly((f-v^2)\u); v=(-v)%u);
  return([u,v%u]);
}
addpair(A,B,f)={
  my(u=A[1],v=A[2],U=B[1],V=B[2]);
  my(a=gcdext(u,U), b=gcdext(a[3],v+V), d=b[3]);
  my(h=monicpoly((u*U)\d^2));
  my(w=((b[1]*a[1]*u*V+b[1]*a[2]*U*v+b[2]*(v*V+f))\d)%h);
  if((w^2-f)%h!=0,error("invalid composition"));
  return(reducepair(h,w,f));
}
multiple(m,A,f)={
  my(B=[1,0]);
  while(m,if(m%2,B=addpair(B,A,f));m=m\2;if(m,A=addpair(A,A,f)));
  return(B);
}
check()={
  my(F=x^7-823507,A=[x-7,-6],k=Mod(1,5));
  if(multiple(9,k*A,k*F)!=[1,0],error("reduction of 9P"));
  my(D=multiple(3,A,F), E=multiple(12,A,F));
  if(k*D!=k*E,error("residue mismatch"));
  my(u=k*D[1],v=k*D[2],du=k*((E[1]-D[1])/5));
  my(line=vector(3,i,-polcoef(lift(Mod(x^(i-1)*du,u)/Mod(2*v,u)),2)));
  if(lift(line)!=[4,0,3],error("unexpected line"));
  print("Cantor tangent ",lift(line));
}
iferr(check(),E,print(E);quit(1));
quit
