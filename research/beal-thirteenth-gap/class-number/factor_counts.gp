\\ Independent norm enumeration in the polynomial power basis.
\\ Output columns: ideal norm, number of distinct primes of that norm.
enumerate() = {
  my(P=x^21+2*x^14-16*x^7+8,T=2^22);
  my(fractions=[[2,[3]],[7,[3]],[13,[1,2,2,2]]]);
  my(N=nfinit(P));
  if(N.disc!=-(2^18*7^21*13^14) || N.sign!=[3,9],error("field"));
  if(setminus(Set(factor(abs(poldisc(P)))[,1]),[2,7,13])!=[],error("index support"));
  for(i=1,#fractions,
    my(q=fractions[i][1],degrees=vecsort(apply(p->p.f,idealprimedec(N,q))));
    if(degrees!=fractions[i][2],error("ramification at ",q));
    for(j=1,#degrees,print(q^degrees[j]," 1"));
  );
  forprime(q=2,T-1,
    if(q==2 || q==7 || q==13,next);
    if(q^2>=T,
      my(c=#polrootsmod(P,q));
      if(c,print(q," ",c)),
      my(factors=factormod(P,q));
      for(i=1,matsize(factors)[1],
        my(n=q^poldegree(factors[i,1]));
        if(factors[i,2]!=1,error("unexpected multiple factor"));
        if(n<T,print(n," 1"));
      );
    );
  );
}
iferr(enumerate(),E,print(E);quit(1));
quit
