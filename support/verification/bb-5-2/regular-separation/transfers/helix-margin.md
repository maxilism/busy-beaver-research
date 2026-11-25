# Right-heavy checkpoints and an equality test in the five-state helix

25 November 2026

Use the table of #4817065 and its canonical tape convention. Write $\Rightarrow$ for a finite run, $\overline B$ for B scanning the bit immediately to its left, and $\alpha$ for $A01\Rightarrow01A$. We use the following checkpoints with blank exterior when no further suffix is displayed.

$$
T(f,m)=f(10)^m1A0,\qquad
P(f,b,c)=fD0(10)^b0\,1^c,\qquad
Q(f,b,c)=fD00(10)^b1^c.
$$

When a suffix follows a displayed word in a calculation below, it is part of the tape. The common up calculation and the down rule leave the tape beyond the displayed final ones alone. A down with a suffix can be checked directly in the down row of Table 1, which only needs the two zeros at the end of its alternating scan. In the common up row $c\ge3$ provides the three right ones needed to turn. A zero exit followed by a right suffix lands on the last zero supplied by the displayed $Q$. When the ensuing entry needs a zero beyond that scanned cell, we supply it explicitly. [Sweep rules and Table 1](https://github.com/maxilism/busy-beaver-research/blob/ee693aa3127ca2aaa09a37f22e8b846fa6048914/results/bb-5-2/cubic-helix.pdf)

## On a right-heavy input the B-start table reaches A on its rightmost one

For all $0\le a<c$ with $a,c$ multiples of three, the run from $Q(1\,0^a,0,c)$ reaches a configuration with A scanning the rightmost one. This guard is useful for machines which follow the helix until an A1 transition finds a blank right exterior.

Define $Q^+(f,b,c)$ as the configuration one D0 step after $Q(f,b,c)$. First note a local formula for any word $f$, integer $d\ge0$ and suffix $Z$. From $Q(f,d,2)\,0Z$, a D0 step and $d+1$ copies of $\alpha$ leave $j1A1\,0Z$, with $j=f(10)^{d+1}$. The three steps A1, C0, D0 then give $j11A0Z$. In particular, if $Z=(10)^b1^e$, this is $Q^+(j1,b,e)$. The single zero between the terminal ones and $Z$ is the only bit needed for this turn. With a blank exterior at $Q(f,d,2)$, the A1 reached by the first part already scans the rightmost one.

### The two reductions at the left margin

For $b\ge0$, $c\ge3$, and $n\ge1$ congruent to one modulo three, the table gives

$$
\begin{aligned}
 Q(1,b,c)&\Rightarrow Q^+(100(10)^1 1,b+1,c-3),\\
 Q(100(10)^n1,b,c)&\Rightarrow Q^+(100(10)^{n+3}1,b,c-3).
\end{aligned}
$$

Each calculation begins with D0 and takes additional steps, so the reductions compose from $Q^+$ as well.

Put $S=(10)^{b+2}1^{c-3}$. The common up row from $Q(f,b,c)$ gives $f\overline B\,0S$. We use $01\overline B\Rightarrow\overline B10$ (B1, E0), $10\overline B\Rightarrow\overline B01$ (B0, C1), $000\overline B\Rightarrow D001$ (B0, C0), and $D001\Rightarrow10D0$ (D0, A0, B1, E1).

For the first reduction $f=1$. Use left blank padding and the Table 1 ending $00001\overline B\Rightarrow10D010$. The word is $10D0(10)0S$. One down gives $100D00\,1S$. The first one of $S$ makes the adjacent ones a block of two, so this is $Q(100,0,2)$ followed by $0(10)^{b+1}1^{c-3}$. The local formula above gives the first reduction.

For the second reduction write $f=100(10)^n1=10(01)^{n+1}$. Move the bar left through the $n+1$ copies of $01$ and then through $10$. Use $000\overline B\Rightarrow D001$ in the blank margin and $D001\Rightarrow10D0$ twice. This gives $(10)^2D0(10)^{n+1}0S$. Do $n+1$ downs. Including the first one of $S$ gives $Q(101\,0^{n+2},0,n+2)$ followed by $0(10)^{b+1}1^{c-3}$.

Since $3\mid n+2$, exactly $(n+2)/3$ ordinary ups and the zero exit give $T(101,n+2)$ with that same suffix. The ending-one entry uses the first zero of the suffix as its right margin. The word becomes $P(100,n+2,1)$ followed by $(10)^{b+1}1^{c-3}$. Do $n+2$ downs and include the first one of the remaining alternating block. This gives $Q(1\,0^{n+4},0,n+4)$ followed by $0(10)^b1^{c-3}$. Another $(n+2)/3$ ups leave $Q(100,n+2,2)$ with that suffix. The local formula gives $Q^+(100(10)^{n+3}1,b,c-3)$. All counts allow $n=1$, $b=0$ and $c=3$.

### Reaching the rightmost one

Starting at $Q(1\,0^a,0,c)$, take $a/3$ ordinary ups to $Q(1,a,p)$, where $p=c-a\ge3$. Use the first reduction once and the second $(p-3)/3$ times. This reaches $Q^+(100(10)^{p-2}1,a+1,0)$. In particular $p=3$ uses precisely the first reduction. Write $h=100(10)^{p-2}$. The zero exit finishes at $T(h1,a+1)$, the ending-one entry gives $P(h0,a+1,1)$, and $a+1$ downs give $Q(h0^{a+2},0,a+2)$. Now $a/3$ ups give $Q(h00,a,2)$ with a blank exterior on the right. The initial D0 and $a+1$ right tiles put A on the rightmost one as claimed.

The same argument also applies to the equal-block vertices of this family once the left bank is lengthened by a multiple $p\ge6$ rather than shortened. The four-zero entry in the sibling proof gives $Q(h100,a,2)$ with blank right exterior. This last configuration reaches A on its rightmost one. [Left-heavy calculation](siblings.md)

## A regular slice with exact equality

Let $h$ be any binary word. For positive multiples $a,c$ of three, consider $X_h(a,c)=Q(h10001\,0^a,0,c)$. If $a\ne c$ the configuration halts. If $a=c$, it reaches $T(h,c+5)$.

* For $a<c$, take $a/3$ ordinary ups. The common up row from $Q(h10001,a,c-a)$ applies since $c-a\ge3$. It leaves B scanning the final one of $10001$. B1, E0, B0, C0 take D to the first one of $10001$, which halts.
* For $a>c$, $c/3$ ups and the zero exit reach $T(h10001\,0^{a-c},c)$. If $a-c=3$, the common entry leaves the final marked substring $10001\overline B$ and the same four moves halt. If $a-c\ge6$, the four-zero entry and the residual-two lemma from the sibling proof force a halt with any left context. [Residual-two lemma and separation proof](../data/cubic-helix-blank-roots.pdf)
* For $a=c$, the zero exit lands at $T(h10001,c)$. The ending-one entry, $c$ downs, $c/3$ ups and the exit at one reach $T(h10000,c+1)$. Apply the gap-four repair from Lemma 3 of the A-start paper, with its fixed extra prefix $h$ carried along. The two entries consume only the displayed gap of four zeros and their displayed ending one, so this gives $T(h10,c+4)=T(h,c+5)$. [Gap-four repair](https://github.com/maxilism/busy-beaver-research/blob/ee693aa3127ca2aaa09a37f22e8b846fa6048914/results/bb-5-2/cubic-helix.pdf)

For example, take $h=(10)^j$, $j\ge0$. The equality case lands on $R(m)=T(\varepsilon,m)$ with $m=c+5+j$. If $m\equiv2\pmod3$ it is an A-orbit return, and if $m\equiv1\pmod3$ it is a B-orbit return. If $m\equiv0\pmod3$ the four-zero entry, $m+1$ downs and $m/3$ ups from $R(m)$ give $Q(100,m,2)$ and halt. Thus on this three-block regular slice the input runs forever exactly when $a=c$ and $j\not\equiv1\pmod3$. [A returns](https://github.com/maxilism/busy-beaver-research/blob/ee693aa3127ca2aaa09a37f22e8b846fa6048914/results/bb-5-2/cubic-helix.pdf) · [B returns and residual-two halts](../data/cubic-helix-blank-roots.pdf)

A separate raw-table replay checked the first reduction and the second reduction for $b=0,\ldots,4$, $c=3,\ldots,10$ and $n=1,4,7$. It also checked all 15 prefixes $h$ of length at most three and all $a,c\in\{3,6,9,12\}$. All 60 equal inputs reached the stated continuation and all 180 unequal inputs halted. The reductions above establish the unbounded statements.
