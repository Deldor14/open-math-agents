# Un profilo scalare con un tratto costante da 1 a 8/5

Sia \(H\) l'interpolante affine dei sette nodi seguenti, prolungato con \(H(t)=t/2\) per \(t\ge16\).

| \(t\) | 0 | 2 | 3 | 5 | 8 | 15 | 16 |
|---|---:|---:|---:|---:|---:|---:|---:|
| \(H(t)\) | 0 | 2 | 2 | 4 | 4 | 8 | 8 |

Il profilo \(F(x)=H(5x)/4\) è continuo e non decrescente su \([0,\infty)\). Vale \(F(x)=5x/4\) fino a \(2/5\), \(F(x)=1\) su tutto \([1,8/5]\) e \(F(x)=5x/8\) da \(16/5\) in avanti. Per ogni \(a,b\ge0\) soddisfa
\[
 F(a+b)\le F(a)+F(b)\le F(a+b+\max(a,b)).
\]

Per verificare le due disuguaglianze basta usare \(H\) e ordinare gli argomenti \(x\le y\). Per \(p=1,2\), le rette \(x=t,\ y=t,\ x+py=t\), con \(t\) tra le ascisse dei nodi, dividono il triangolo \(0\le x\le y\le16\) in celle sulle quali \(H(x)+H(y)-H(x+py)\) è affine. Il verificatore razionale controlla il segno ai 43 vertici per \(p=1\) e ai 44 vertici per \(p=2\), inclusi quelli sulla diagonale \(x=y\). Se \(x\le16\le y\) il primo scarto resta costante al crescere di \(y\), il secondo diminuisce di \((y-16)/2\) rispetto al valore sulla frontiera. Per \(16\le x\le y\) tutti gli argomenti sono nel tratto \(H(t)=t/2\).

Il profilo soddisfa anche tutti i vincoli digitali
\[
  R_3(m)\,F(x)\le F((2m-1)x),\qquad m\ge1,\quad x\ge0.
\]
Per \(m=1\) si ha uguaglianza. Per \(m=2\) si usa l'incollamento con \(a=b=x\). Per \(m\ge3\) l'insieme di tutti gli \(m\) interi contiene la progressione \(1,2,3\), quindi \(R_3(m)\le m-1\). I nodi e l'interpolazione danno \(t/2\le H(t)\le t\); ne segue \(H((2m-1)t)\ge(m-1/2)t\ge R_3(m)H(t)\).

Vale quindi anche il modulo degli incrementi derivato dalla costruzione di Behrend. Se \((2m-1)h\le x\), allora \(R_3(m)(F(x+h)-F(x))\le R_3(m)F(h)\le F(x)\).

L'esempio mostra che questi vincoli, assunti da soli, sono compatibili con \(F(8/5)=F(1)>0\). Per dedurne la crescita stretta dei veri numeri di Roth a questa dilatazione occorre sfruttare altra struttura.
