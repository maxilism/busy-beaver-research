"""Small sparse automata over arbitrary hashable labels. None is epsilon."""
from collections import defaultdict, deque

class NFA:
    def __init__(self):
        self.e = [defaultdict(set)]; self.f = set()
    def new(self):
        self.e.append(defaultdict(set)); return len(self.e)-1
    def edge(self,i,c,j): self.e[i][c].add(j)
    def path(self,i,word,j):
        if not word: self.edge(i,None,j)
        for p,c in enumerate(word):
            k = j if p+1==len(word) else self.new()
            self.edge(i,c,k); i=k
    def dfa(self):
        def closure(states):
            seen=set(states); stack=list(seen)
            while stack:
                for j in self.e[stack.pop()].get(None,()):
                    if j not in seen: seen.add(j); stack.append(j)
            return frozenset(seen)
        def moves(q):
            d=defaultdict(set)
            for i in q:
                for c,js in self.e[i].items():
                    if c is not None: d[c].update(js)
            return ((c,closure(js)) for c,js in d.items())
        return build(closure([0]),lambda s: not s.isdisjoint(self.f),moves)

class DFA:
    def __init__(self,t,f): self.t=t; self.f=set(f)
    def __len__(self): return len(self.t)
    def trim_min(self):
        # Bog-standard backwards liveness then partition refinement. Missing edge = sink.
        rev=[set() for _ in self.t]
        for i,row in enumerate(self.t):
            for j in row.values(): rev[j].add(i)
        live=set(self.f); stack=list(live)
        while stack:
            for i in rev[stack.pop()]-live: live.add(i); stack.append(i)
        if not 0 in live: return DFA([{}],set())
        order=[0]+sorted(live-{0}); states={i:int(i in self.f) for i in order}
        while True:
            ids={}; nxt={}
            for i in order:
                key=(i in self.f,frozenset((c,states[j]) for c,j in self.t[i].items() if j in live))
                nxt[i]=ids.setdefault(key,len(ids))
            if states==nxt: break
            states=nxt
        rows=[{} for _ in ids]
        for i,g in states.items(): rows[g]={c:states[j] for c,j in self.t[i].items() if j in live}
        return DFA(rows,{states[i] for i in self.f})

def build(start,accept,moves):
    states=[start]; ids={start:0}; n=NFA()
    # May be nondeterministic; do not call n.dfa recursively in the deterministic case.
    det=True
    for i,q in enumerate(states):
        if accept(q): n.f.add(i)
        for c,y in moves(q):
            if y not in ids: ids[y]=n.new(); states.append(y)
            if c is None or (c in n.e[i] and ids[y] not in n.e[i][c]): det=False
            n.edge(i,c,ids[y])
    if not det:return n.dfa()
    return DFA([{c:next(iter(v)) for c,v in row.items()} for row in n.e],n.f).trim_min()

def union(*ds):
    n=NFA()
    for d in ds:
        off=len(n.e)
        for _ in d.t:n.new()
        n.edge(0,None,off); n.f.update(off+i for i in d.f)
        for i,row in enumerate(d.t):
            for c,j in row.items(): n.edge(off+i,c,off+j)
    return n.dfa()

def project(d,fn):
    return build(0,lambda i:i in d.f,lambda i:((fn(c),j) for c,j in d.t[i].items()))

def difference_witness(d,e):
    """Shortest witness in L(d) - L(e), else None; number of explored pairs."""
    start=(0,0); todo=deque([start]); prev={start:None}
    while todo:
        p,q=todo.popleft()
        if p in d.f and q not in e.f:
            x=(p,q); w=[]
            while prev[x] is not None:
                x,c=prev[x]; w.append(c)
            return list(reversed(w)),len(prev)
        for c,t in d.t[p].items():
            u=e.t[q].get(c,-1) if q!=-1 else -1; nxt=(t,u)
            if nxt not in prev: prev[nxt]=((p,q),c); todo.append(nxt)
    return None,len(prev)

def incl(tag,d,e):
    w,n=difference_witness(d,e)
    if w is not None: raise ValueError(f'{tag}: witness {w!r}')
    print(f'{tag}: OK [{len(d)} -> {len(e)} states; {n} reachable product pairs]',flush=True)

def expr(parts):
    """Sequence of (word, repeat?) with repeat=True meaning Kleene star."""
    n=NFA(); p=0
    for w,star in parts:
        q=n.new()
        if star:n.edge(p,None,q); n.path(q,w,q)
        else:n.path(p,w,q)
        p=q
    n.f={p}; return n.dfa()
