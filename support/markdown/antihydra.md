# Halting inputs in every size progression for Antihydra

maxilism

24 November 2026

The BB(6) holdout Antihydra has transition table

```
1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA
```

The groups give the instructions for states `A` through `F`, first on zero and then on one; `---` halts. It is machine 9785, line 36 of the [30 October 2026 holdout list](https://wiki.bbchallenge.org/w/images/5/5e/BB6_holdouts_608.txt). [Shawn Ligocki's 2024 account](https://www.sligocki.com/2024/07/06/bb-6-2-is-hard.html) credits mxdys with finding the machine and Racheline with its early return rules. Using the [formally verified acceleration in Google DeepMind's `cryptids` library](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean#L597-L661), we find in each size progression at fixed reserve a subprogression whose inputs halt within a bounded number of return-map attempts. The result rules out a context-free language separating the blank trajectory from configurations that eventually halt. It leaves the fate of the blank run open.

## Size growth and reserve changes by parity

In the notation of the verified program, $P(a,b,c)$ has tape $1^a0\,1^b[F1]1^c$, surrounded by zeros. The token $[F1]$ marks the one scanned in state `F`. Counting from the blank start at time zero, the literal table reaches $P(0,3,1)$ after 12 transitions. Take the section $P(a,b,1)$ with integers $a\ge0$, $b\ge1$, and put $u=b+4$. One **attempt** means running from this section until its next return or halt. For $b\ge3$ an internal transition reduces $b$ by two and adds three to $c$. Starting at $b=2k+1$ or $2k+2$, exactly $k$ such transitions precede the respective exit at $b=1$ or $b=2$. The two exit rules give

| Current size | Next $(a,b)$ or outcome |
|---|---|
| $b=2k+1$ | $(a+2,3k+4)$ |
| $b=2k+2$, $a>0$ | $(a-1,3k+5)$ |
| $b=2k+2$, $a=0$ | halt |

Thus the size alone follows $u'=\lceil 3u/2\rceil$. An odd $u$ earns two units of reserve $a$; an even $u$ spends one and halts if $a=0$. The Lean theorem `is_valid_acceleration` proves each transition and the halting case on arbitrary encoded configurations. This off-blank scope is needed below; a run observed only from $(a,u)=(0,7)$ would not suffice.

## Halting subprogressions at fixed reserve

**Proposition.** Fix integers $a\ge0$, $b_0\ge1$ and $M\ge1$. Write $t=v_2(M)$, the exponent of two in $M$. Among the sizes $b=b_0+Mk$, $k\ge0$, an entire arithmetic subprogression halts from $P(a,b,1)$ in at most $a+3t+1$ attempts.

Write $u_j(k)$ for the size after $j$ successful returns starting at $b_0+Mk$. While the prefix survives, its size differences satisfy

$$u_j(k)-u_j(0)=3^j2^{t-j}(M/2^t)k,\qquad 0\le j\le t.$$

At $j=0$ the difference is $Mk$. For $j<t$ it is even, so the next parity and reserve change are common to every input; on that parity the size update multiplies differences by $3/2$. This proves the formula by induction. If the prefix overdrafts, all halt on the same attempt. Otherwise the common reserve at $j=t$ is $h\le a+2t$, and the coefficient of $k$ in $u_t(k)$ is now odd. Set $s=h+1$ and choose the unique residue of $k$ modulo $2^s$ for which $2^s$ divides $u_t(k)$. The next $s$ sizes are even: before each attempted step there remains a factor of two, and the size update on that branch is exactly $3u/2$. The $s$th loss halts. This gives stride $M2^s$ in $b$ and at most $t+s\le a+3t+1$ attempts. It also covers $M$ odd, when the forced prefix is empty.

For example the blank section has $a=0$, $b=3$. On the progression $b=3+4k$ the first two gains take the reserve to 4 and the size to $17+9k$. Making that size a multiple of 32 selects $k\equiv23\pmod {32}$. Thus $b=95+128j$ halts on its seventh attempt.

## No context-free separator on marked tapes

Encode a configuration up to translation by trimming outer zeros and retaining the marked scanned cell. On this section, a finite-state transducer can read a word $X^aY^b$ and output the tape $1^a0\,1^b[F1]1$, omitting the leading unscanned zero when $a=0$. If a context-free language separated all blank-reached tapes from all tapes leading to halt, its inverse image on $X^*Y^+$ would still be context-free. By [Parikh's theorem](https://doi.org/10.1145/321356.321364), the corresponding set $S$ of exponent pairs $(a,b)$ would be semilinear: a finite union of translates of finitely generated additive monoids in $\mathbb N^2$.

A generator $(0,d)$ with $d>0$ in any one component puts a whole size progression at fixed reserve in $S$, contradicting the proposition. All other nonzero generators have positive first coordinate; taking their largest slope and accounting for the finitely many base points gives $b\le C(a+1)$ on $S$ for some $C$. If blank survives through $i$ returns, however, $a_i\le2i$ while $b_i+4\ge7(3/2)^i$. A surviving blank trajectory cannot fit in $S$. If blank halts, its own configurations already lie on both sides of the proposed separation. The reverse orientation, with a context-free language containing the halting side and excluding the reached side, fails as well: complement its **semilinear set of exponent pairs** inside the section, where semilinear sets are closed under complement. No closure of context-free languages under complement is required.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
