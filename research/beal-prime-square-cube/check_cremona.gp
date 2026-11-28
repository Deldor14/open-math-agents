\\ Supply [N,a1,a2,a3,a4,a6] for all rows whose conductor has
\\ exactly one prime >3, with multiplicity one. End with the integer zero.
audit() = {
  my(line, v, E, J, p, k, U, V, n=0, seen=Map());
  while ((line=input()) != 0,
    v=line; n++;
    p=v[1]; p=p/2^valuation(p,2); p=p/3^valuation(p,3);
    if (!isprime(p), next);
    E=ellinit(v[2..6]); J=E.j/1728;
    if(J<=0 || J>=1,next);
    if(!ispower(denominator(J), , &U), next);
    k=valuation(denominator(J),p);
    if(k<3 || denominator(J)!=p^k,next);
    if(ispower(numerator(J),3,&V) && issquare(numerator(1-J),&U),
      mapput(seen,[p,k,U,V],1));
  );
  print(n); print(Vec(seen));
}
