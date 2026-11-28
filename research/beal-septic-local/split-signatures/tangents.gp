testTangent(p,t)={
  my(g=(p-1)/2, u=(t+1)*(t+2), W=6+t-2*t^2, y=2*t+3);
  my(Z=vector(g,i,Mod(i,p)),r=vector(g,i,(Z[i]^2-1)/(4*u)));
  my(T=vector(g,i,(Z[i]+1)/2));
  my(mat=matrix(g,g,j,i,r[i]^(j-1)/Z[i]), target=vectorv(g,j,j*W/y));
  my(b=matsolve(mat,target), L=sum(i=1,g,u/(Z[i]*T[i])*(b[i]^p-r[i]^(p-1)*b[i])));
  if(L==0 || L!=W*u/y^3,error("split tangent"));lift(L)
}
{forprime(p=11,100,if(p%7!=1 && p%7!=6,next);my(roots=polrootsmod(x^3+x^2-2*x-1,p));print(p," ",vector(3,i,testTangent(p,roots[i]))));}
