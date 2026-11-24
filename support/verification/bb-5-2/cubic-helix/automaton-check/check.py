#!/usr/bin/env python3
"""Independent all-length certificate check. Python 3, stdlib only. See README.md."""
import hashlib,json,sys
from itertools import product
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fa import NFA,DFA,build,union,project,incl,expr

bits='01'; states='ABCDE'; cells=list(bits)+[q+x for q in states for x in bits]
tab=dict(zip(states,[('1RB','0RC'),('1LC','0LE'),('0LD','0LB'),('1RA',None),('1LB','0RD')]))
Z='0'*7

def bufparse(pending,s):
    out=[]
    for ch in s:
        if ch in bits: out.append(pending+ch); pending=''
        else:
            assert ch in states and not pending; pending=ch
    return pending,tuple(out)

def pair_spec(parts):
    """Compile a paired parametrization: (old chunk, new chunk[, '*']).
    Each star repeats the *pair* jointly; lag is bounded in all specs here.
    Emits synchronous pairs of cells, consuming marker letters as decorations.
    """
    n=NFA(); start=(0,'','',(),()); qs=[start]; ids={start:0}
    for source in qs:
        i=ids[source]; k,a,b,left,right=source
        if k==len(parts):
            assert not (a or b or left or right), (a,b,left,right)
            n.f.add(i); continue
        x,y,*r=parts[k]; assert r in ([],['*'])
        aa,l=bufparse(a,x); bb,h=bufparse(b,y); l=left+l; h=right+h
        j=min(len(l),len(h)); out=tuple(zip(l[:j],h[:j])); l=l[j:]; h=h[j:]
        assert len(l)+len(h)<16, 'unbounded lag?'
        nxt=[(out,(k if r else k+1,aa,bb,l,h))]
        if r: nxt.append(((),(k+1,a,b,left,right)))
        for w,q in nxt:
            if q not in ids: qs.append(q); ids[q]=n.new()
            n.path(i,w,ids[q])
    return n.dfa()

def same(parts):
    return pair_spec([(p[0],p[0],*p[1:]) for p in parts])

def sources():
    # R, K=D0(P)'s successor, U=D0(Q)'s successor. Fixed physical window.
    r=same([(Z,),('10101',),('010101','*'),('A0'+Z,)])
    ks=[]
    for a in (1,2,3):
        b=(1-a)%3
        ks.append(same([(Z+'1'+'0'*a,),('000','*'),('1A'+'10'*b,),('101010','*'),('0'+'1'*a,),('111','*'),(Z,)]))
    u=same([(Z+'10',),('000','*'),('1A',),('010101','*'),('01',),('111','*'),(Z,)])
    return r,union(*ks),u

def one(q,t,i):
    tr=tab[q][int(t[i])]; assert tr is not None,(q,t,i)
    y,move,s=tr; t[i]=y
    return s,i+(1 if move=='R' else -1)

def decorated(t,q,i):
    assert 0<=i<len(t); z=t[:]; z[i]=q+t[i]; return z

def parse_marked(s):
    j,q=next((j,c) for j,c in enumerate(s) if c not in bits)
    assert q in ('A','b'); return q.upper(),j-(q=='b'),list(s[:j]+s[j+1:])

def local_pairs(examples):
    """Union of pair words in arbitrary unchanged plain-bit contexts."""
    n=NFA(); end=n.new(); n.f={end}
    for x in bits: n.edge(0,(x,x),0); n.edge(end,(x,x),end)
    for s,t in examples:
        assert len(s)==len(t); n.path(0,list(zip(s,t)),end)
    return n.dfa()

def atom(lhs,rhs,count):
    # Include exterior adjacent cells iff an endpoint scans there (b before
    # first bit, or A after last bit). Check that *every* step stays inside
    # this minimal footprint; other exterior bits are completely irrelevant.
    left=bits if lhs.startswith('b') or rhs.startswith('b') else ['']
    right=bits if lhs.endswith('A') or rhs.endswith('A') else ['']
    paths=[]
    for l,r in product(left,right):
        q,i,t=parse_marked(l+lhs+r); before=decorated(t,q,i)
        for _ in range(count):
            assert 0<=i<len(t); q,i=one(q,t,i)
        qq,j,u=parse_marked(l+rhs+r)
        assert (qq,j,u)==(q,i,t),(lhs,rhs,l,r,q,i,t)
        paths.append((before,decorated(t,q,i)))
    return local_pairs(paths)

def single():
    paths=[]
    for q in states:
        for x,h in product(bits,repeat=2):
            rule=tab[q][int(x)]
            if rule is None: continue
            i=int(rule[1]=='L'); t=[h,x] if i else [x,h]
            before=decorated(t,q,i); p,j=one(q,t,i); paths.append((before,decorated(t,p,j)))
    return local_pairs(paths)

def sweeps():
    # positive-k explicit relations, plus identity. Exactly one decorated cell.
    n=NFA(); s=n.new(); n.f={s}
    for x in bits:n.edge(0,(x,x),0); n.edge(s,(x,x),s)
    for x in cells[2:]:n.edge(0,(x,x),s)
    ident=n.dfa(); out=[]
    for kind in ['right','01left','10left']:
        n=NFA(); f=n.new(); n.f={f}
        for x in bits: n.edge(0,(x,x),0); n.edge(f,(x,x),f)
        p=n.new()
        if kind=='right':
            n.path(0,[('A0','0'),('1','1')],p)
            n.path(p,[('0','0'),('1','1')],p)
            for z in bits:n.edge(p,(z,'A'+z),f)
        else:
            x,y='01' if kind=='01left' else '10'
            for z in bits:n.edge(0,(z,'B'+z),p)
            n.path(p,[(x,y),(y,x)],p)
            n.path(p,[(x,y),('B'+y,x)],f)
        out.append(union(ident,n.dfa()))
    return out

def then(rel,op):
    """Composition (x,y) with (y,z), projected to (x,z) on the fly."""
    idx=[]
    for row in op.t:
        by={}
        for (y,z),n in row.items():by.setdefault(y,[]).append((z,n))
        idx.append(by)
    def moves(s):
        p,q=s
        for (x,y),pp in rel.t[p].items():
            for z,qq in idx[q].get(y,()): yield (x,z),(pp,qq)
    return build((0,0),lambda s:s[0] in rel.f and s[1] in op.f,moves)

def image(d,op):
    lifted=project(d,lambda x:(x,x)); return target(then(lifted,op))
def target(d): return project(d,lambda pair:pair[1])

def keep_first(rel,allowed):
    def moves(s):
        p,q=s
        for (x,y),pp in rel.t[p].items():
            if x in allowed.t[q]: yield (x,y),(pp,allowed.t[q][x])
    return build((0,0),lambda s:s[0] in rel.f and s[1] in allowed.f,moves)

def prescribed_returns():
    """Exact paired endpoint *requirements*: not images forgetting lengths."""
    # Entry: 4 left margin cells and one right margin cell become active.
    entry=pair_spec([(Z[:-4],Z[:-4]),('00001','101A10'),('01','10','*'),('A00','01'),(Z[1:],Z[1:])])
    front=[(Z+'1',Z+'1'),('0','0','*')]
    # m down: (m-1) alternating blocks retained; a -> a+1 and r -> r+1.
    down=pair_spec(front+[('1A10','01A'),('10','10','*'),('0','01'),('1','1','*'),(Z,Z)])
    # Ordinary up only, gap has three available zeros, r >= 3.
    up=pair_spec(front+[('0001A','1A010101'),('01','01','*'),('0111','0'),('1','1','*'),(Z,Z)])
    # r=1 exit: moves right past k+1 blocks, includes one more scanned blank.
    exit1=pair_spec(front+[('1A','1'),('01','01','*'),('010','01A0'),(Z[1:],Z[1:])])
    return entry,down,up,exit1

def phase_domains(R):
    # Independently write entire source projections of the four obligations.
    # Even if a paired endpoint expression lost a residue branch or parameter
    # value, a domain inclusion should detect the hole.
    front=[(Z+'1',)]; end=[(Z,)]
    down=[]
    for gap in [1,2,3]:
        least_positive_b=(3-gap)%3+1 # the positive b with b+gap=1 mod 3
        down.append(same(front+[('0'*gap,),('000','*'),('1A'+'10'*least_positive_b,),('101010','*'),('0'+'1'*gap,),('111','*')]+end))
    up=same(front+[('0000',),('000','*'),('1A',),('010101','*'),('01111',),('111','*')]+end)
    exit1=same(front+[('0',),('000','*'),('1A',),('010101','*'),('01',)]+end)
    return list(map(target,(R,union(*down),up,exit1)))

def canonical_words(padded):
    # Erase arbitrary zero prefixes/suffixes, expand cells into alphabet
    # 01ABCDE, and require first & last retained cells are not plain zero.
    d=padded; n=NFA(); f=n.new(); n.f={f}
    for row in d.t: n.new()
    off=2
    for row in d.t: n.new()
    off2=off+len(d)
    # Interior copy, two copies distinguished by whether the last cell may end.
    for i,row in enumerate(d.t):
        for c,j in row.items():
            for base in [off,off2]: n.path(base+i,c,(off if c=='0' else off2)+j)
    q=0; seen=set()
    while q not in seen:
        seen.add(q)
        for c,j in d.t[q].items():
            if c!='0': n.path(0,c,off2+j)
        if '0' not in d.t[q]:break
        q=d.t[q]['0']
    for i in range(len(d)):
        q=i; seen=set()
        while q not in seen:
            if q in d.f: n.edge(off2+i,None,f); break
            seen.add(q)
            if '0' not in d.t[q]: break
            q=d.t[q]['0']
    return n.dfa()

def blank_prefix():
    ones=set(); i=0; q='A'; ds=[]
    for t in range(15):
        lo=min(ones|{i}); hi=max(ones|{i}); tape=[str(int(p in ones)) for p in range(lo,hi+1)]
        w=''.join(decorated(tape,q,i-lo)); ds.append(expr([(w,False)]))
        if t<14:
            y,dir,q=tab[q][int(i in ones)]
            if y=='1':ones.add(i)
            else:ones.discard(i)
            i+=1 if dir=='R' else -1
    assert w=='10101A0'; return union(*ds)

def shipped(path):
    blob=path.read_bytes(); h=hashlib.sha256(blob).hexdigest(); print('shipped sha256:',h)
    if h!='123cdce7aaa1a27daa78cd2ee04c8c02de3dafe5043f4c2eef766a7fdd938b4d': raise ValueError('wrong file')
    a=json.loads(blob); assert a['alphabet']=='01ABCDE' and a['missing']==-1 and a['initial']==0
    assert len(a['delta'])==176; return DFA([{c:j for c,j in zip(a['alphabet'],row) if j>=0} for row in a['delta']],a['final'])

def main():
    if not __debug__: raise SystemExit('Run without -O: this checker uses assertions.')
    if len(sys.argv)>2: raise SystemExit('Usage: python3 check.py [dfa.json]')
    path=(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'dfa.json')
    d=shipped(path); R,K,U=sources(); right,L,M=sweeps()
    fwd=atom('A01','01A',4); bend=atom('A10','1A0',3); turn=atom('A00','b01',3)
    v=atom('A11','0b0',2); l=atom('01b','b10',2); finish=atom('11b','01A',3); start=atom('000b','1A01',3)
    # M's underlying left atom, independently replayed too.
    atom('10b','b01',2)
    programs=[(R,[turn,L,l,start,fwd]),(K,[bend,right,turn,L,finish]),(U,[right,v,M,start]),(U,[right])]
    pts=[]
    for (src,ops),want,expected,tag in zip(programs,prescribed_returns(),phase_domains(R),['entry','down','up','exit']):
        curr=src; pts.append(target(src))
        for op in ops: curr=then(curr,op); pts.append(target(curr))
        need=keep_first(want,target(src)); assert need.f
        dom=project(need,lambda pair:pair[0])
        incl(tag+' full required domain',expected,dom)
        incl(tag+' paired endpoints contained in complete program',need,curr)
    cuts=union(*pts); ds=[cuts]; step=single()
    for _ in range(3): ds.append(image(ds[-1],step))
    cover=union(canonical_words(union(*ds)),blank_prefix())
    incl('shipped subset of independent safe language',d,cover)
    incl('independent selected interpolation subset of shipped',cover,d)
    for w,ans in [('10D001111',False),('101A01111',True)]:
        state=0
        for c in w: state=d.t[state].get(c,-1) if state>=0 else -1
        assert (state in d.f)==ans
    print('Broader construction witness: rejects 10D001111 in S; accepts its successor 101A01111.')
    print('PASS. Endpoint inclusions retain BOTH tape tracks. Equality is for selected interpolation only.')
if __name__=='__main__': main()
