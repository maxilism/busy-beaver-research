# A quadratic time bound for a two-state Turing machine on finite input

maxilism

Let a deterministic machine have two working states, a two-way binary tape, and a one-cell move left or right at each nonhalting step. Include the halting instruction in the step count. Suppose the initial head and every nonblank cell lie in an interval of length $L\ge1$. **If the machine halts, the initial interval and the entire head trajectory fit in $W=6L+30$ cells, and it halts within $2W^2+3$ steps.** The order $L^2$ is attained on a family of finite inputs to a single table.

Finite-input decidability is classical. See [Pavlotskaya (1973)](https://doi.org/10.1007/BF01163965) and [Kudlek, *Small deterministic Turing machines* (1996)](https://doi.org/10.1016/S0304-3975(96)00078-3). [Neary and Woods, §3.4](https://arxiv.org/abs/1110.2230), credit K. Wagner (*Elektronische Informationsverarbeitung und Kybernetik* **9**, 1973, 423–431) with an asymptotic linear space bound. We give explicit constants on an ordinary one-dimensional tape. They allow composition with a five-state machine running from blank.

## Which state graphs need a time estimate?

In the graph of nonhalting transitions, weight right edges by $+1$ and left edges by $-1$. A run visits each strongly connected component in a single phase. First consider a visited component whose cycles do not have both signs. Reflect if necessary to make all cycle weights nonnegative. Give each vertex a zero-weight edge **from** an auxiliary source and let $h(q)$ be the negative of its shortest-path distance. A shortest path can be simple, so $0\le h\le1$ for two states ($h=0$ for one). In state $q$ at position $x$ the coordinate $s=x+h(q)$ is nondecreasing on internal transitions, by the shortest-path inequality. The head stays in $[s-1,s]$.

Let the old interval be $[l,r]$ of length $S$, with blank tape outside. At each level $s<r$ a halter has at most eight configurations before a transition: a repeated state and two-cell window would repeat the segment at that level. At all levels $s\ge r$ **together** the same bound holds. The tape beyond $s$ is blank, and the machine can no longer read below $s-1$. Equal windows and states there replay the intervening segment translated, indefinitely. Since $s\ge l$, the phase costs at most $8S$, including exit. Its head stays at or above $l-1$ before exit. Once $s\ge r$, there are at most eight more moves, and the head cannot first enter this range beyond $r+1$. Thus even including an exit move the span grows by at most 12. If the run visits two singleton components, their internal moves are individually monotone after reflection. A singleton can take at most $S+1$ steps through exit: past the old interval it reads fresh blanks and must exit at once or move forever. Its phase adds at most two cells to the span. These estimates imply the stated width and time bounds for every halter visiting only components of this kind. A singleton with cycles of both signs has both rows internal and can never halt or exit.

In a two-vertex component with cycles of both signs, a halter needs one halt row. Its state, call it $A$, has exactly one internal edge, to the other state $D$. If both edges out of $D$ went to $A$, every simple cycle would contain the fixed move out of $A$, so opposite signs would be impossible. Thus $D$ has a loop and an edge to $A$, and the two-step cycle must move twice opposite to the loop. Reflect so the loop moves right. Name the letters $u,v$ by their roles at $D$; either may be blank. From a checkpoint in $D$ at $p$ the two possible macros are

| letter | action | next checkpoint |
|---|---|---|
| $u$ | write $w$ | $p+1$ |
| $v$ | write $z$; test the cell at $p-1$ in $A$ | if it is $a$, write $y$ and go to $p-2$; otherwise halt |

A successful left macro rewrites the pair $av$ as $yz$, in left-to-right order. If the machine starts in $A$, execute one step first. Unless it halts there, the resulting starting interval $[l,r]$, including the old one, has length $N\le L+1$.

## How far can the mixed component travel?

If $w\ne a$, attempting a left macro just after a right one halts on the just-written $w$. All successful left macros therefore precede the right moves. On the left leg, once both cells read are fresh blanks, the machine jumps left forever, fails the test, or begins its right leg. On the right leg, the first virgin cell beyond $r$ either starts a failed left macro or begins an infinite right scan. The interval $[l-5,r+3]$ suffices. For the remaining cases assume $w=a$.

**Blank $u$.** A checkpoint beyond $r$ on a fresh $u$ escapes right. On the other side, a first left jump to a new minimum $m<l$ lands on fresh $u$. Every previous intermediate cell in a successful macro was between its two checkpoints. If $y=v$, the new cell sends the head right, writing $a$, to the $v$ just written at $m+1$. Its left jump over $a$ lands on the next fresh $u$ and repeats the motion forever. For $y=u$ there are three possibilities:

* If $a=u$, no new $v$ is created, so a left jump starts inside the original interval and lands at or above $l-2$.
* If $a=v,z=u$, a right move adds one $v$ and a left jump removes two. The invariant $p-\#v$ gives $p\ge l-N$.
* If $a=v,z=v$, the cells at $m+1,m+2$ now contain $u,v$. Two right moves and one left jump return to $m$, now marked $v$. The next test fails on the fresh $u$ at $m-1$.

**Blank $v$.** At a first new left minimum below $l$, both the scanned cell and the one to its left are fresh $v$. The test fails if $a=u$, and otherwise the head jumps left forever. For the right edge consider the following four cases.

* If $a=v$, the quantity $p+\#u$ never increases: a right move consumes a $u$ and a left jump creates at most two. Thus $p\le r+N$.
* If $a=u,z=v$, the virgin $v$ at $r+1$ cannot become $u$ before the head has crossed it, since its $D$-write is $v$ and $A$ can reach it only from the right. A right crossing requires $u$.
* If $a=u,z=u,y=u$, every $u$ is permanent. At a first arrival at $r+3$ the two preceding cells are $u$ since both were used for right moves. A left jump converts the virgin $v$ to $u$; three right moves then meet the next virgin $v$ with the same two-cell suffix, giving infinite drift.
* If $a=u,z=u,y=v$, take the rightmost cell in the following four-cell window to be $p$, with brackets marking the head in state $D$. A left jump acts by

  $$
  c_1\;c_2\;u\;[D:v] \quad\longmapsto\quad c_1\;[D:c_2]\;v\;u .
  $$

  This pushes one of at most $N$ ordered $u$-particles one cell right. If $c_1=c_2=v$, the next left test fails. Thus on every nonlast push there is an earlier particle at $p-2$ or $p-3$; the pushed particle finishes at most three cells beyond its predecessor. Particle 1 makes no nonlast push. By induction particle $i$ stays at or below $r+3(i-1)$ before the last push. The last push adds at most one. Every right move starts at a particle, so $p\le r+3N+2$.

A common interval, allowing the intermediate test and a final halt move, is $[l-N-5,r+3N+5]$. Its width $5N+10$ is less than $6L+30$.

## Time in the mixed component

Number the cells of a containing interval from $0$ to $W-1$. All symbol counts and sums in this time estimate refer only to these cells, even when the letter being counted is blank. Between the first and last $D$-checkpoints write $S$ for the number of right moves, $P$ for the number of successful left pairs, and $\delta$ for head displacement. The elapsed time is

$$
 S+2P=\delta+4P,\qquad \delta=S-2P.
$$

For $w\ne a$ the two monotone legs cost at most $2(W-1)$. For $w=a=u$, right moves leave the tape alone. If the left rewrite $uv\mapsto yz$ is the identity, no checkpoint position repeats on a halter. If it gives $uu$ or $vv$, one letter count decreases per pair, so $P\le W$. If it gives $vu$, the sum of positions of the $u$'s increases by one per pair, so $P\le W(W-1)/2$. In all cases time is at most $2W^2$, using $|\delta|\le W-1$ (a successful left pair requires $W\ge3$).

For $w=a=v$, each right move creates one $v$ and each left pair removes a fixed number $k\in\{0,1,2\}$ of them. If $k\le1$, their change in number satisfies $\Delta\#v-\delta=(2-k)P$. Substitution in $\delta+4P$ gives at most $7W-3\le2W^2$ for $W\ge3$. For $k=2$ use the potential

$$
 \Phi(p)=p^2-2\sum_{i:\,\mathrm{cell}\ i=v} i .
$$

A right move changes it by $(p+1)^2-p^2-2p=1$. A left pair erasing $v$'s at $p-1,p$ changes it by $(p-2)^2-p^2+2(p-1)+2p=2$. Its increase equals the elapsed time, and its range has length at most $(W-1)^2+W(W-1)<2W^2$. Allow one step from an initial $A$ and two for the final failed pair. This proves the clock.

**Quadratic example.** Take `1RA0LB_1RZ0LA`, with row order $A,B$, column order $0,1$, and $Z$ halt. Start in $A$ at the first cell of $0\,1^j\,0\,1$ on a zero background. For $0\le i\le j$ the machine reaches $A$ at $-i$ with just the ones in $[i+1,j]$ and at $j+2$. For $i<j$, it takes $2i+1$ right moves through position $i$, then $i+1$ left pairs erase the resulting even block and land at $-i-1$. At $i=j$ it takes $2j+2$ right moves, $j+1$ successful left pairs and a failed pair. The total is $\sum_{i<j,\ i\ge0}(4i+3)+4j+6=2j^2+5j+6$ steps on input width $j+3$.

**Seven-state application.** Suppose five states contain the start and the other two form a closed set: the four entries there may halt or stay within the pair. Replace each entrance to the pair by a halt. The resulting five-state blank machine agrees until its halt or that entrance, which on a halting run occurs within $B=47{,}176{,}870$ steps by the [BB(5) theorem](https://arxiv.org/abs/2509.12337). At entrance the original head and all nonblank cells fit in $B+1$ cells. Applying the clock with $W=6(B+1)+30=283{,}061{,}256$ gives at most **160,247,349,343,771,945 steps** including the prelude.

© 2026 maxilism. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
