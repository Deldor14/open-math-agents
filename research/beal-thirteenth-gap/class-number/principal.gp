\\ B and the two endpoints are initialized by replay.py.
verify_range(B, first, last, T) = {
  my(total=0);
  forprime(q=first,last,
    my(degrees=logint(T-1,q), primes=idealprimedec(B,q,degrees));
    for(i=1,#primes,
      my(pr=primes[i], g=bnfisprincipal(B,pr,3)[2], norm=q^pr.f);
      if(norm>=T || idealhnf(B,g)!=idealhnf(B,pr),
        error("principal ideal equality failed at ",[q,i]));
      print(norm);
      total++;
    );
  );
  print("OK ",total);
}
