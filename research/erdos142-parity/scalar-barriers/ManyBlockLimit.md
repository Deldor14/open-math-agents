# Erdős 142. Un limite per la costruzione con più intervalli

Sia \(k\ge 3\). Consideriamo \(n+1\ge 3\) intervalli interi disgiunti e ordinati, di lunghezze positive \(w_0,\dots,w_n\). Il vuoto \(g_i\ge 0\) conta gli interi strettamente tra l'intervallo \(i\) e il successivo. Supponiamo che ogni scelta indipendente di sottoinsiemi privi di progressioni aritmetiche non costanti di \(k\) termini dia un'unione ancora priva di tali progressioni. Poniamo \(W=\sum_i w_i\) e \(G=\sum_i g_i\). Allora

\[
             2W \le (2k-3)(G+n).
\]

**Il vincolo locale.** Consideriamo due intervalli adiacenti di lunghezze \(w,v>0\), con un vuoto di \(g\) interi. La progressione di passo \(s=g+1\) che contiene l'ultimo punto del primo e il primo del secondo incontra rispettivamente \(C=1+\lfloor(w-1)/s\rfloor\) e \(E=1+\lfloor(v-1)/s\rfloor\) punti consecutivi. Se \(C+E\ge k\), prendiamo gli ultimi \(c=\min(C,k-1)\) termini nel primo intervallo e i primi \(k-c\) nel secondo. Allora \(1\le c<k\) e \(1\le k-c\le E\). I due sottoinsiemi hanno ognuno meno di \(k\) punti e la loro unione contiene una progressione di lunghezza \(k\). Negli intervalli restanti possiamo scegliere l'insieme vuoto. Dunque \(C+E\le k-1\), anche per \(g=0\). Da \(w\le Cs,\ v\le Es\) e \(C,E\ge1\) segue

\[
        w+v\le(k-1)s,\qquad w,v\le(k-2)s.
\]

**Somma sugli intervalli.** Sommando il primo vincolo sulle \(n\) coppie adiacenti si ottiene \(2W-w_0-w_n\le(k-1)(G+n)\). Gli estremi sono accanto a due vuoti distinti, perciò \(w_0+w_n\le(k-2)(g_0+1+g_{n-1}+1)\le(k-2)(G+n)\). Sommando le due disuguaglianze si ottiene la stima.

**Confronto con due intervalli.** Per \(n\) fisso e \(W\to\infty\), o più generalmente per \(n/W\to0\), il rapporto fra la lunghezza totale e la parte occupata soddisfa

\[
   \liminf \frac{W+G}{W}\ \ge\ 1+\frac{2}{2k-3}
       \ >\ \frac{1+\sqrt{1+4/(k-2)}}{2}.
\]

Per la disuguaglianza stretta scriviamo \(h=k-2\) e \(d=(\sqrt{1+4/h}-1)/2\). Da \(hd(1+d)=1\) e \(h\ge1\) segue \(0<d<1\). Di conseguenza \(hd>1/2\) e, moltiplicando per \(d\), si trova \(d(2h+1)<2\). La stima riguarda la costruzione che permette sottoinsiemi arbitrari e indipendenti in ciascun intervallo. Se i sottoinsiemi devono soddisfare vincoli reciproci, il passo locale richiede un altro argomento.

**Numero di intervalli variabile.** Anche quando \(n\) cresce liberamente con la lunghezza \(L=W+G\), l'ipotesi globale consente di scegliere un singoletto in ciascun intervallo. I \(n+1\) rappresentanti formano un insieme privo di progressioni di \(k\) termini, dunque \(n+1\le R_k(L)\). La forma qualitativa del teorema di Szemerédi dà \(R_k(L)/L\to0\) per ogni \(k\) fissato. Sostituendo \(G=L-W\) nella stima finita si trova
\[
 (2k-1)W \le (2k-3)(L+n)
 \quad\Longrightarrow\quad
 \limsup_{L\to\infty}\frac{W}{L} \le \frac{2k-3}{2k-1}.
\]
Ne segue il medesimo limite inferiore per la dilatazione anche per queste famiglie.

Il file «ManyBlockLimit.lean» verifica il vincolo locale, la somma sugli intervalli, la disuguaglianza fra le due soglie e il limite finito per il numero dei rappresentanti. I nomi dei quattro teoremi nel namespace «Erdos142ManyBlock» sono «adjacent_capacity», «many_block_limit», «strictly_above_two_block» e «representatives_bound».
