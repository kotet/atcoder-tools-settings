// dfmt off
T lread(T=long)(){return readln.chomp.to!T;}T[] lreads(T=long)(long n){return iota(n).map!((_)=>lread!T).array;}
T[] aryread(T=long)(){return readln.split.to!(T[]);}void arywrite(T)(T a){a.map!text.join(' ').writeln;}
void scan(L...)(ref L A){auto l=readln.split;foreach(i,T;L){A[i]=l[i].to!T;}}alias sread=()=>readln.chomp();
void dprint(L...)(lazy L A){debug{auto l=new string[](L.length);static foreach(i,a;A)l[i]=a.text;arywrite(l);}}
alias PQueue(T,alias l="b<a")=BinaryHeap!(Array!T,l);import std, core.bitop;
// dfmt on
{% if mod %}
immutable long MOD = {{ mod }};
{% endif %}
{% if yes_str %}
immutable string YES = "{{ yes_str }}";
{% endif %}
{% if no_str %}
immutable string NO = "{{ no_str }}";
{% endif %}
void main()
{
    {% if prediction_success %}
    {{ input_part }}
    solve({{ actual_arguments }});
    {% else %}
    // Failed to predict input format
    {% endif %}
}

{% if prediction_success %}
void solve({{ formal_arguments }})
{

}
{% endif %}

// --- lazy_segtree ---

struct LazySegTree(S, alias op, alias e, F, alias mapping, alias composition, alias id)
{
    import std.functional : unaryFun, binaryFun;
    import std.traits : isCallable, Parameters;

    static if (is(typeof(e) : string))
    {
        auto unit()
        {
            return mixin(e);
        }
    }
    else
    {
        alias unit = e;
    }
    static if (is(typeof(id) : string))
    {
        auto identity()
        {
            return mixin(id);
        }
    }
    else
    {
        alias identity = id;
    }
public:
    this(int n)
    {
        auto v = new S[](n);
        v[] = unit();
        this(v);
    }

    this(const S[] v)
    {
        _n = cast(int) v.length;
        log = celiPow2(_n);
        size = 1 << log;
        assert(1 <= size);
        d = new S[](2 * size);
        d[] = unit();
        lz = new F[](size);
        lz[] = identity();
        foreach (i; 0 .. _n)
            d[size + i] = v[i];
        foreach_reverse (i; 1 .. size)
            update(i);
    }

    void set(int p, S x)
    {
        assert(0 <= p && p < _n);
        p += size;
        foreach_reverse (i; 1 .. log + 1)
            push(p >> i);
        d[p] = x;
        foreach (i; 1 .. log + 1)
            update(p >> i);
    }

    S get(int p)
    {
        assert(0 <= p && p < _n);
        p += size;
        foreach_reverse (i; 1 .. log + 1)
            push(p >> i);
        return d[p];
    }

    S prod(int l, int r)
    {
        assert(0 <= l && l <= r && r <= _n);
        if (l == r)
            return unit();
        l += size;
        r += size;
        foreach_reverse (i; 1 .. log + 1)
        {
            if (((l >> i) << i) != l)
                push(l >> i);
            if (((r >> i) << i) != r)
                push(r >> i);
        }

        S sml = unit(), smr = unit();
        while (l < r)
        {
            if (l & 1)
                sml = binaryFun!(op)(sml, d[l++]);
            if (r & 1)
                smr = binaryFun!(op)(d[--r], smr);
            l >>= 1;
            r >>= 1;
        }

        return binaryFun!(op)(sml, smr);
    }

    S allProd()
    {
        return d[1];
    }

    void apply(int p, F f)
    {
        assert(0 <= p && p < _n);
        p += size;
        foreach_reverse (i; 1 .. log + 1)
            push(p >> i);
        d[p] = binaryFun!(mapping)(f, d[p]);
        foreach (i; 1 .. log + 1)
            update(p >> i);
    }

    void apply(int l, int r, F f)
    {
        assert(0 <= l && l <= r && r <= _n);
        if (l == r)
            return;
        l += size;
        r += size;
        foreach_reverse (i; 1 .. log + 1)
        {
            if (((l >> i) << i) != l)
                push(l >> i);
            if (((r >> i) << i) != r)
                push((r - 1) >> i);
        }
        {
            int l2 = l, r2 = r;
            while (l < r)
            {
                if (l & 1)
                    all_apply(l++, f);
                if (r & 1)
                    all_apply(--r, f);
                l >>= 1;
                r >>= 1;
            }
            l = l2;
            r = r2;
        }
        foreach (i; 1 .. log + 1)
        {
            if (((l >> i) << i) != l)
                update(l >> i);
            if (((r >> i) << i) != r)
                update((r - 1) >> i);
        }
    }

    int maxRight(alias g)(int l)
    {
        return maxRight(l, unaryFun!(g));
    }

    int maxRight(G)(int l, G g) if (isCallable!G && Parameters!(G).length == 1)
    {
        assert(0 <= l && l <= _n);
        assert(g(unit()));
        if (l == _n)
            return _n;
        l += size;
        foreach_reverse (i; 1 .. log + 1)
            push(l >> i);
        S sm = unit();
        do
        {
            while (l % 2 == 0)
                l >>= 1;
            if (!g(binaryFun!(op)(sm, d[l])))
            {
                while (l < size)
                {
                    push(l);
                    l = 2 * l;
                    if (g(binaryFun!(op)(sm, d[l])))
                    {
                        sm = binaryFun!(op)(sm, d[l]);
                        l++;
                    }
                }
                return l - size;
            }
            sm = binaryFun!(op)(sm, d[l]);
            l++;
        }
        while ((l & -l) != l);
        return _n;
    }

    int minLeft(alias g)(int r)
    {
        return minLeft(r, unaryFun!(g));
    }

    int minLeft(G)(int r, G g) if (isCallable!G && Parameters!(G).length == 1)
    {
        assert(0 <= r && r <= _n);
        assert(g(unit()));
        if (r == 0)
            return 0;
        r += size;
        foreach_reverse (i; 1 .. log + 1)
            push((r - 1) >> i);
        S sm = unit();
        do
        {
            r--;
            while (r > 1 && (r % 2))
                r >>= 1;
            if (!g(binaryFun!(op)(d[r], sm)))
            {
                while (r < size)
                {
                    push(r);
                    r = (2 * r + 1);
                    if (g(binaryFun!(op)(d[r], sm)))
                    {
                        sm = binaryFun!(op)(d[r], sm);
                        r--;
                    }
                }
                return r + 1 - size;
            }
            sm = binaryFun!(op)(d[r], sm);
        }
        while ((r & -r) != r);
        return 0;
    }

private:
    int _n = 0, size = 1, log = 0;
    S[] d = [unit(), unit()];
    F[] lz = [identity()];

    void update(int k)
    {
        d[k] = binaryFun!(op)(d[2 * k], d[2 * k + 1]);
    }

    void all_apply(int k, F f)
    {
        d[k] = binaryFun!(mapping)(f, d[k]);
        if (k < size)
            lz[k] = binaryFun!(composition)(f, lz[k]);
    }

    void push(int k)
    {
        all_apply(2 * k, lz[k]);
        all_apply(2 * k + 1, lz[k]);
        lz[k] = identity();
    }
}
// --- internal_scc ---

struct CompressedSparseRow(E)
{
    import std.typecons : Tuple;

    int[] start;
    E[] elist;
    this(int n, const ref Tuple!(int, E)[] edges) @safe nothrow
    {
        start = new typeof(start)(n + 1);
        elist = new typeof(elist)(edges.length);
        foreach (e; edges)
            start[e[0] + 1]++;
        foreach (i; 0 .. n)
            start[i + 1] += start[i];
        auto counter = start.dup;
        foreach (e; edges)
            elist[counter[e[0]]++] = e[1];
    }
}

struct SccGraphImpl
{
    import std.typecons : Tuple;
    import std.algorithm : min;

public:
    this(int n) @safe nothrow @nogc
    {
        _n = n;
    }

    int numVerticles() @safe nothrow @nogc
    {
        return _n;
    }

    void addEdge(int from, int to) @safe nothrow
    {
        edges ~= Tuple!(int, edge)(from, edge(to));
    }

    Tuple!(int, int[]) sccIds() @safe nothrow
    {
        auto g = CompressedSparseRow!(edge)(_n, edges);
        int now_ord = 0, group_num = 0;
        int[] visited;
        auto low = new int[](_n);
        auto ord = new int[](_n);
        ord[] = -1;
        auto ids = new int[](_n);
        visited.reserve(_n);
        void dfs(int v)
        {
            low[v] = ord[v] = now_ord++;
            visited ~= v;
            foreach (i; g.start[v] .. g.start[v + 1])
            {
                auto to = g.elist[i].to;
                if (ord[to] == -1)
                {
                    dfs(to);
                    low[v] = min(low[v], low[to]);
                }
                else
                {
                    low[v] = min(low[v], ord[to]);
                }
            }
            if (low[v] == ord[v])
            {
                while (true)
                {
                    int u = visited[$ - 1];
                    visited.length--;
                    ord[u] = _n;
                    ids[u] = group_num;
                    if (u == v)
                        break;
                }
                group_num++;
            }
        }

        foreach (i; 0 .. _n)
            if (ord[i] == -1)
                dfs(i);
        foreach (ref x; ids)
            x = group_num - 1 - x;
        return Tuple!(int, int[])(group_num, ids);
    }

    int[][] scc() @safe nothrow
    {
        auto ids = sccIds();
        int group_num = ids[0];
        auto counts = new int[](group_num);
        foreach (x; ids[1])
            counts[x]++;
        auto groups = new int[][](ids[0]);
        foreach (i; 0 .. group_num)
            groups[i].reserve(counts[i]);
        foreach (i; 0 .. _n)
            groups[ids[1][i]] ~= i;
        return groups;
    }

private:
    int _n;
    struct edge
    {
        int to;
    }

    Tuple!(int, edge)[] edges;
}
// --- fenwicktree ---

struct FenwickTree(T)
{
    import std.traits : isSigned, Unsigned;

    static if (isSigned!T)
    {
        alias U = Unsigned!T;
    }
    else
    {
        alias U = T;
    }
public:
    this(int n) @safe nothrow
    {
        _n = n;
        data = new U[](n);
    }

    void add(int p, T x) @safe nothrow @nogc
    {
        assert(0 <= p && p < _n);
        p++;
        while (p <= _n)
        {
            data[p - 1] += cast(U) x;
            p += p & -p;
        }
    }

    T sum(int l, int r) @safe nothrow @nogc
    {
        assert(0 <= l && l <= r && r <= _n);
        return sum(r) - sum(l);
    }

private:
    int _n;
    U[] data;

    U sum(int r) @safe nothrow @nogc
    {
        U s = 0;
        while (r > 0)
        {
            s += data[r - 1];
            r -= r & -r;
        }
        return s;
    }
}
// --- scc ---

struct SccGraph
{
    this(int n) @safe nothrow
    {
        internal = SccGraphImpl(n);
    }

    void addEdge(int from, int to) @safe nothrow
    {
        int n = internal.numVerticles();
        assert(0 <= from && from < n);
        assert(0 <= to && to < n);
        internal.addEdge(from, to);
    }

    int[][] scc() @safe nothrow
    {
        return internal.scc();
    }

private:
    SccGraphImpl internal;
}
// --- internal_math ---

import std.typecons : Tuple;

/// Return: `x mod m`
/// Param: `1 <= m`
ulong safeMod(long x, long m) @safe pure nothrow @nogc
{
    x %= m;
    if (x < 0)
        x += m;
    return x;
}

/// Return: `a*b` (128bit width)
ulong[2] umul128(ulong a, ulong b) @safe @nogc pure nothrow
{
    immutable ulong au = a >> 32;
    immutable ulong bu = b >> 32;
    immutable ulong al = a & ((1UL << 32) - 1);
    immutable ulong bl = b & ((1UL << 32) - 1);

    ulong t = al * bl;
    immutable ulong w3 = t & ((1UL << 32) - 1);
    ulong k = t >> 32;
    t = au * bl + k;

    k = t & ((1UL << 32) - 1);
    immutable ulong w1 = t >> 32;
    t = al * bu + k;
    k = t >> 32;
    return [au * bu + w1 + k, t << 32 + w3];
}

/// Fast modular multiplication by barrett reduction
/// Reference: https://en.wikipedia.org/wiki/Barrett_reduction
/// NOTE: reconsider after Ice Lake
struct Barrett
{
    ///
    uint _m;
    ///
    ulong im;
    /// Param: `1 <= m < 2^31`
    this(uint m) @safe @nogc pure nothrow
    {
        _m = m;
        im = (cast(ulong)(-1)) / m + 1;
    }

    /// Return: `m`
    uint umod() @safe @nogc pure nothrow
    {
        return _m;
    }

    /// Param: `0 <= a < m`, `0 <= b < m`
    /// Return: `a * b % m`
    uint mul(uint a, uint b) @safe @nogc pure nothrow
    {
        ulong z = a;
        z *= b;
        immutable ulong x = umul128(z, im)[0];
        uint v = cast(uint)(z - x * _m);
        if (_m <= v)
            v += _m;
        return v;
    }
}

/// Param: `0 <= n`, `1 <= m`
/// Return: `(x ^^ n) % m`
long ctPowMod(long x, long n, int m) @safe pure nothrow @nogc
{
    if (m == 1)
        return 0;
    uint _m = cast(uint) m;
    ulong r = 1;
    ulong y = safeMod(x, m);
    while (n)
    {
        if (n & 1)
            r = (r * y) % _m;
        y = (y * y) % _m;
        n >>= 1;
    }
    return r;
}

/// Reference:
/// M. Forisek and J. Jancina,
/// Fast Primality Testing for Integers That Fit into a Machine Word
/// Param: `0 <= n`
bool ctIsPrime(int n) @safe pure nothrow @nogc
{
    if (n <= 1)
        return false;
    if (n == 2 || n == 7 || n == 61)
        return true;
    if (n % 2 == 0)
        return false;
    long d = n - 1;
    while (d % 2 == 0)
        d /= 2;
    foreach (a; [2, 7, 61])
    {
        long t = d;
        long y = ctPowMod(a, t, n);
        while (t != n - 1 && y != 1 && y != n - 1)
        {
            y = y * y % n;
            t <<= 1;
        }
        if (y != n - 1 && t % 2 == 0)
        {
            return false;
        }
    }
    return true;
}

/// ditto
enum bool isPrime(int n) = ctIsPrime(n);

/// Param: `1 <= b`
/// Return: `pair(g, x)` s.t. `g = gcd(a, b)`, `x*a = g (mod b)`, `0 <= x < b/g`
Tuple!(long, long) invGcd(long a, long b) @safe pure nothrow @nogc
{
    a = safeMod(a, b);
    if (a == 0)
        return Tuple!(long, long)(b, 0);
    long s = b, t = a, m0 = 0, m1 = 1;
    while (t)
    {
        immutable long u = s / t;
        s -= t * u;
        m0 -= m1 * u;
        long tmp = s;
        s = t;
        t = tmp;
        tmp = m0;
        m0 = m1;
        m1 = tmp;
    }
    if (m0 < 0)
        m0 += b / s;
    return Tuple!(long, long)(s, m0);
}

/// Compile time primitive root
/// Param: m must be prime
/// Return: primitive root (and minimum in now)
int ctPrimitiveRoot(int m) @safe pure nothrow @nogc
{
    if (m == 2)
        return 1;
    if (m == 167_772_161)
        return 3;
    if (m == 469_762_049)
        return 3;
    if (m == 754_974_721)
        return 11;
    if (m == 998_244_353)
        return 3;
    int[20] divs;
    divs[0] = 2;
    int cnt = 1;
    int x = (m - 1) / 2;
    while (x % 2 == 0)
        x /= 2;
    for (int i = 3; (cast(long) i) * i <= x; i += 2)
        if (x % i == 0)
        {
            divs[cnt++] = i;
            while (x % i == 0)
                x /= i;
        }
    if (x > 1)
        divs[cnt++] = x;
    for (int g = 2;; g++)
    {
        bool ok = true;
        foreach (i; 0 .. cnt)
            if (ctPowMod(g, (m - 1) / divs[i], m) == 1)
            {
                ok = false;
                break;
            }
        if (ok)
            return g;
    }
}

/// ditto
enum primitiveRoot(int m) = ctPrimitiveRoot(m);
// --- internal_bit ---

int celiPow2(int n) @safe pure nothrow @nogc
{
    int x = 0;
    while ((1u << x) < cast(uint)(n))
        x++;
    return x;
}
// --- convolution ---

import std.traits : isInstanceOf, isIntegral;

void butterfly(mint)(mint[] a) @safe nothrow @nogc
        if (isInstanceOf!(StaticModInt, mint))
{
    import core.bitop : bsf;

    static immutable int g = primitiveRoot!(mint.mod());
    int n = cast(int) a.length;
    int h = celiPow2(n);

    static bool first = true;
    static mint[30] sum_e;
    if (first)
    {
        first = false;
        mint[30] es, ies;
        int cnt2 = bsf(mint.mod() - 1);
        mint e = mint(g).pow((mint.mod() - 1) >> cnt2);
        mint ie = e.inv();
        foreach_reverse (i; 2 .. cnt2 + 1)
        {
            es[i - 2] = e;
            ies[i - 2] = ie;
            e *= e;
            ie *= ie;
        }
        mint now = 1;
        foreach (i; 0 .. cnt2 - 2 + 1)
        {
            sum_e[i] = es[i] * now;
            now *= ies[i];
        }
    }
    foreach (ph; 1 .. h + 1)
    {
        int w = 1 << (ph - 1), p = 1 << (h - ph);
        mint now = 1;
        foreach (s; 0 .. w)
        {
            int offset = s << (h - ph + 1);
            foreach (i; 0 .. p)
            {
                auto l = a[i + offset];
                auto r = a[i + offset + p] * now;
                a[i + offset] = l + r;
                a[i + offset + p] = l - r;
            }
            now *= sum_e[bsf(~(cast(uint) s))];
        }
    }
}

void butterflyInv(mint)(mint[] a) @safe nothrow @nogc
        if (isInstanceOf!(StaticModInt, mint))
{
    import core.bitop : bsf;

    static immutable int g = primitiveRoot!(mint.mod());
    int n = cast(int) a.length;
    int h = celiPow2(n);

    static bool first = true;
    static mint[30] sum_ie;
    if (first)
    {
        first = false;
        mint[30] es, ies;
        int cnt2 = bsf(mint.mod() - 1);
        mint e = mint(g).pow((mint.mod() - 1) >> cnt2);
        mint ie = e.inv();
        foreach_reverse (i; 2 .. cnt2 + 1)
        {
            es[i - 2] = e;
            ies[i - 2] = ie;
            e *= e;
            ie *= ie;
        }
        mint now = 1;
        foreach (i; 0 .. cnt2 - 2 + 1)
        {
            sum_ie[i] = ies[i] * now;
            now *= es[i];
        }
    }

    foreach_reverse (ph; 1 .. h + 1)
    {
        int w = 1 << (ph - 1), p = 1 << (h - ph);
        mint inow = 1;
        foreach (s; 0 .. w)
        {
            int offset = s << (h - ph + 1);
            foreach (i; 0 .. p)
            {
                auto l = a[i + offset];
                auto r = a[i + offset + p];
                a[i + offset] = l + r;
                a[i + offset + p] = mint(cast(ulong)(mint.mod() + l.val() - r.val()) * inow.val());
            }
            inow *= sum_ie[bsf(~(cast(uint) s))];
        }
    }
}

mint[] convolution(mint)(mint[] a, mint[] b) @safe nothrow 
        if (isInstanceOf!(StaticModInt, mint))
{
    import std.algorithm : min, swap;

    int n = cast(int) a.length, m = cast(int) b.length;
    if (!n || !m)
        return [];
    if (min(n, m) <= 60)
    {
        if (n < m)
        {
            swap(n, m);
            swap(a, b);
        }
        auto ans = new mint[](n + m - 1);
        foreach (i; 0 .. n)
            foreach (j; 0 .. m)
                ans[i + j] += a[i] * b[j];
        return ans;
    }
    int z = 1 << celiPow2(n + m - 1);
    a.length = z;
    butterfly(a);
    b.length = z;
    butterfly(b);
    foreach (i; 0 .. z)
        a[i] *= b[i];
    butterflyInv(a);
    a.length = n + m - 1;
    mint iz = mint(z).inv();
    foreach (i; 0 .. n + m - 1)
        a[i] *= iz;
    return a;
}

T[] convolution(uint mod = 998_244_353, T)(T[] a, T[] b) @safe nothrow 
        if (isIntegral!(T))
{
    int n = cast(int)(a.length), m = cast(int)(b.length);
    if (!n || !m)
        return [];
    alias mint = StaticModInt!(mod);
    auto a2 = new mint[](n), b2 = new mint[](m);
    foreach (i; 0 .. n)
        a2[i] = mint(a[i]);
    foreach (i; 0 .. m)
        b2[i] = mint(b[i]);
    auto c2 = convolution(a2, b2);
    auto c = new T[](n + m - 1);
    foreach (i; 0 .. n + m - 1)
        c[i] = c2[i].val();
    return c;
}

long[] convolutionLL(long[] a, long[] b) @safe nothrow
{
    int n = cast(int)(a.length), m = cast(int)(b.length);
    if (!n || !m)
        return [];
    static immutable ulong MOD1 = 90 * (2 ^^ 23) + 1;
    static immutable ulong MOD2 = 10 * (2 ^^ 24) + 1;
    static immutable ulong MOD3 = 14 * (2 ^^ 25) + 1;
    static assert(MOD1 == 754_974_721 && MOD2 == 167_772_161 && MOD3 == 469_762_049);
    static immutable ulong M2M3 = MOD2 * MOD3;
    static immutable ulong M1M3 = MOD1 * MOD3;
    static immutable ulong M1M2 = MOD1 * MOD2;
    static immutable ulong M1M2M3 = MOD1 * MOD2 * MOD3;
    static immutable ulong i1 = invGcd(MOD2 * MOD3, MOD1)[1];
    static immutable ulong i2 = invGcd(MOD1 * MOD3, MOD2)[1];
    static immutable ulong i3 = invGcd(MOD1 * MOD2, MOD3)[1];

    auto c1 = convolution!(MOD1)(a, b);
    auto c2 = convolution!(MOD2)(a, b);
    auto c3 = convolution!(MOD3)(a, b);

    auto c = new long[](n + m - 1);
    foreach (i; 0 .. n + m - 1)
    {
        ulong x;
        x += (c1[i] * i1) % MOD1 * M2M3;
        x += (c2[i] * i2) % MOD2 * M1M3;
        x += (c3[i] * i3) % MOD3 * M1M2;
        long diff = c1[i] - safeMod(cast(long) x, cast(long) MOD1);
        if (diff < 0)
            diff += MOD1;
        static immutable ulong[5] offset = [0, 0, M1M2M3, 2 * M1M2M3, 3 * M1M2M3];
        x -= offset[diff % 5];
        c[i] = x;
    }
    return c;
}
// --- segtree ---

struct Segtree(S, alias op, alias e)
{
    import std.functional : binaryFun, unaryFun;
    import std.traits : isCallable, Parameters;

    static if (is(typeof(e) : string))
    {
        auto unit()
        {
            return mixin(e);
        }
    }
    else
    {
        alias unit = e;
    }

    this(int n)
    {
        auto buf = new S[](n);
        buf[] = unit();
        this(buf);
    }

    this(S[] v)
    {
        _n = cast(int) v.length;
        log = celiPow2(_n);
        size = 1 << log;
        d = new S[](2 * size);
        d[] = unit();
        foreach (i; 0 .. _n)
            d[size + i] = v[i];
        foreach_reverse (i; 1 .. size)
            update(i);
    }

    void set(int p, S x)
    {
        assert(0 <= p && p < _n);
        p += size;
        d[p] = x;
        foreach (i; 1 .. log + 1)
            update(p >> i);
    }

    S get(int p)
    {
        assert(0 <= p && p < _n);
        return d[p + size];
    }

    S prod(int l, int r)
    {
        assert(0 <= l && l <= r && r <= _n);
        S sml = unit(), smr = unit();
        l += size;
        r += size;
        while (l < r)
        {
            if (l & 1)
                sml = binaryFun!(op)(sml, d[l++]);
            if (r & 1)
                smr = binaryFun!(op)(d[--r], smr);
            l >>= 1;
            r >>= 1;
        }
        return binaryFun!(op)(sml, smr);
    }

    S allProd()
    {
        return d[1];
    }

    int maxRight(alias f)(int l)
    {
        return maxRight(l, &unaryFun!(f));
    }

    int maxRight(F)(int l, F f) if (isCallable!F && Parameters!(F).length == 1)
    {
        assert(0 <= l && l <= _n);
        assert(f(unit()));
        if (l == _n)
            return _n;
        l += size;
        S sm = unit();
        do
        {
            while (l % 2 == 0)
                l >>= 1;
            if (!f(binaryFun!(op)(sm, d[l])))
            {
                while (l < size)
                {
                    l = 2 * l;
                    if (f(binaryFun!(op)(sm, d[l])))
                    {
                        sm = binaryFun!(op)(sm, d[l]);
                        l++;
                    }
                }
                return l - size;
            }
            sm = binaryFun!(op)(sm, d[l]);
            l++;
        }
        while ((l & -l) != l);
        return _n;
    }

    int minLeft(alias f)(int r)
    {
        return minLeft(r, &unaryFun!(f));
    }

    int minLeft(F)(int r, F f) if (isCallable!F && Parameters!(F).length == 1)
    {
        assert(0 <= r && r <= _n);
        assert(f(unit()));
        if (r == 0)
            return 0;
        r += size;
        S sm = unit();
        do
        {
            r--;
            while (r > 1 && (r % 2))
                r >>= 1;
            if (!f(binaryFun!(op)(d[r], sm)))
            {
                while (r < size)
                {
                    r = 2 * r + 1;
                    if (f(binaryFun!(op)(d[r], sm)))
                    {
                        sm = binaryFun!(op)(d[r], sm);
                        r--;
                    }
                }
                return r + 1 - size;
            }
            sm = binaryFun!(op)(d[r], sm);
        }
        while ((r & -r) != r);
        return 0;
    }

private:
    int _n = 0, size = 1, log = 0;
    S[] d = [unit(), unit()];
    void update(int k)
    {
        d[k] = binaryFun!(op)(d[2 * k], d[2 * k + 1]);
    }
}
// --- math ---

import std.typecons : Tuple;

long powMod(long x, long n, long m) @safe pure nothrow @nogc
{
    assert(0 <= n && 1 <= m);
    if (m == 1)
        return 0;
    Barrett bt = Barrett(cast(uint) m);
    uint r = 1, y = cast(uint) safeMod(x, m);
    while (n)
    {
        if (n & 1)
            r = bt.mul(r, y);
        y = bt.mul(y, y);
        n >>= 1;
    }
    return r;
}

long invMod(long x, long m) @safe pure nothrow @nogc
{
    assert(1 <= m);
    auto z = invGcd(x, m);
    assert(z[0] == 1);
    return z[1];
}

Tuple!(long, long) crt(long[] r, long[] m) @safe pure nothrow @nogc
{
    assert(r.length == m.length);
    long r0 = 0, m0 = 1;
    foreach (i; 0 .. r.length)
    {
        assert(1 <= m[i]);
        long r1 = safeMod(r[i], m[i]);
        long m1 = m[i];
        if (m0 < m1)
        {
            auto tmp = r0;
            r0 = r1;
            r1 = tmp;
            tmp = m0;
            m0 = m1;
            m1 = tmp;
        }
        if (m0 % m1 == 0)
        {
            if (r0 % m1 != r1)
                return Tuple!(long, long)(0, 0);
            continue;
        }
        long g, im;
        {
            auto tmp = invGcd(m0, m1);
            g = tmp[0];
            im = tmp[1];
        }
        long u1 = m1 / g;
        if ((r1 - r0) % g)
            return Tuple!(long, long)(0, 0);
        long x = (r1 - r0) / g % u1 * im % u1;
        r0 += x * m0;
        m0 *= u1;
        if (r0 < 0)
            r0 += m0;
    }
    return Tuple!(long, long)(r0, m0);
}

long floorSum(long n, long m, long a, long b) @safe pure nothrow @nogc
{
    long ans;
    if (m <= a)
    {
        ans += (n - 1) * n * (a / m) / 2;
        a %= m;
    }
    if (m <= b)
    {
        ans += n * (b / m);
        b %= m;
    }
    long y_max = (a * n + b) / m, x_max = (y_max * m - b);
    if (y_max == 0)
        return ans;
    ans += (n - (x_max + a - 1) / a) * y_max;
    ans += floorSum(y_max, a, m, (a - x_max % a) % a);
    return ans;
}
// --- acl ---
// --- mincostflow ---

struct MCFGraph(Cap, Cost)
{
    import std.typecons : Tuple;

public:
    this(int n)
    {
        _n = n;
        g = new _edge[][](n);
    }

    int addEdge(int from, int to, Cap cap, Cost cost)
    {
        assert(0 <= from && from < _n);
        assert(0 <= to && to < _n);
        assert(0 <= cap);
        assert(0 <= cost);
        int m = cast(int) pos.length;
        pos ~= Tuple!(int, int)(from, cast(int) g[from].length);
        int from_id = cast(int) g[from].length;
        int to_id = cast(int) g[to].length;
        if (from == to)
            to_id++;
        g[from] ~= _edge(to, to_id, cap, cost);
        g[to] ~= _edge(from, from_id, 0, -cost);
        // g[from] ~= _edge(to, (cast(int) g[to].length), cap, cost);
        // g[to] ~= _edge(from, (cast(int) g[from].length) - 1, 0, -cost);
        return m;
    }

    struct Edge
    {
        int from, to;
        Cap cap, flow;
        Cost cost;
    }

    Edge getEdge(int i)
    {
        int m = cast(int) pos.length;
        assert(0 <= i && i < m);
        auto _e = g[pos[i][0]][pos[i][1]];
        auto _re = g[_e.to][_e.rev];
        return Edge(pos[i][0], _e.to, _e.cap + _re.cap, _re.cap, _e.cost);
    }

    Edge[] edges()
    {
        int m = cast(int) pos.length;
        auto result = new Edge[](m);
        foreach (i; 0 .. m)
            result[i] = getEdge(i);
        return result;
    }

    Tuple!(Cap, Cost) flow(int s, int t)
    {
        return flow(s, t, Cap.max);
    }

    Tuple!(Cap, Cost) flow(int s, int t, Cap flow_limit)
    {
        return slope(s, t, flow_limit)[$ - 1];
    }

    Tuple!(Cap, Cost)[] slope(int s, int t)
    {
        return slope(s, t, Cap.max);
    }

    Tuple!(Cap, Cost)[] slope(int s, int t, Cap flow_limit)
    {
        import std.container : Array, BinaryHeap;
        import std.algorithm : min;

        assert(0 <= s && s < _n);
        assert(0 <= t && t < _n);
        assert(s != t);
        auto dual = new Cost[](_n);
        auto dist = new Cost[](_n);
        auto pv = new int[](_n);
        auto pe = new int[](_n);
        auto vis = new bool[](_n);
        bool dualRef()
        {
            dist[] = Cost.max;
            pv[] = -1;
            pe[] = -1;
            vis[] = false;
            struct Q
            {
                Cost key;
                int to;
                int opCmp(const Q other) const
                {
                    if (key == other.key)
                        return 0;
                    return key > other.key ? -1 : 1;
                }
            }

            BinaryHeap!(Array!Q) que;
            dist[s] = 0;
            que.insert(Q(0, s));
            while (!que.empty)
            {
                int v = que.front.to;
                que.removeFront();
                if (vis[v])
                    continue;
                vis[v] = true;
                if (v == t)
                    break;
                foreach (i; 0 .. cast(int) g[v].length)
                {
                    auto e = g[v][i];
                    if (vis[e.to] || !e.cap)
                        continue;
                    Cost cost = e.cost - dual[e.to] + dual[v];
                    if (dist[e.to] - dist[v] > cost)
                    {
                        dist[e.to] = dist[v] + cost;
                        pv[e.to] = v;
                        pe[e.to] = i;
                        que.insert(Q(dist[e.to], e.to));
                    }
                }
            }
            if (!vis[t])
                return false;
            foreach (v; 0 .. _n)
            {
                if (!vis[v])
                    continue;
                dual[v] -= dist[t] - dist[v];
            }
            return true;
        }

        Cap flow = 0;
        Cost cost = 0, prev_cost_per_flow = -1;
        Tuple!(Cap, Cost)[] result;
        result ~= Tuple!(Cap, Cost)(flow, cost);
        while (flow < flow_limit)
        {
            if (!dualRef())
                break;
            Cap c = flow_limit - flow;
            for (int v = t; v != s; v = pv[v])
                c = min(c, g[pv[v]][pe[v]].cap);
            for (int v = t; v != s; v = pv[v])
            {
                g[pv[v]][pe[v]].cap -= c;
                g[v][g[pv[v]][pe[v]].rev].cap += c;
            }
            Cost d = -dual[s];
            flow += c;
            cost += c * d;
            if (prev_cost_per_flow == d)
                result.length--;
            result ~= Tuple!(Cap, Cost)(flow, cost);
            prev_cost_per_flow = d;
        }
        return result;
    }

private:
    int _n;
    struct _edge
    {
        int to, rev;
        Cap cap;
        Cost cost;
    }

    Tuple!(int, int)[] pos;
    _edge[][] g;
}
// --- maxflow ---

struct MFGraph(Cap)
{
    import std.typecons : Tuple;

public:
    this(int n)
    {
        _n = n;
        g = new _edge[][](n);
    }

    int addEdge(int from, int to, Cap cap)
    {
        assert(0 <= from && from < _n);
        assert(0 <= to && to < _n);
        assert(0 <= cap);
        int m = cast(int) pos.length;
        pos ~= Tuple!(int, int)(from, cast(int)(g[from].length));
        int from_id = cast(int) g[from].length;
        int to_id = cast(int) g[to].length;
        if (from == to)
            to_id++;
        g[from] ~= _edge(to, to_id, cap);
        g[to] ~= _edge(from, from_id, 0);
        return m;
    }

    struct Edge
    {
        int from, to;
        Cap cap, flow;
    }

    Edge getEdge(int i)
    {
        int m = cast(int)(pos.length);
        assert(0 <= i && i < m);
        auto _e = g[pos[i][0]][pos[i][1]];
        auto _re = g[_e.to][_e.rev];
        return Edge(pos[i][0], _e.to, _e.cap + _re.cap, _re.cap);
    }

    Edge[] edges()
    {
        int m = cast(int)(pos.length);
        Edge[] result;
        foreach (i; 0 .. m)
            result ~= getEdge(i);
        return result;
    }

    void changeEdge(int i, Cap new_cap, Cap new_flow)
    {
        int m = cast(int)(pos.length);
        assert(0 <= i && i < m);
        assert(0 <= new_flow && new_flow <= new_cap);
        auto _e = &g[pos[i][0]][pos[i][1]];
        auto _re = &g[_e.to][_e.rev];
        _e.cap = new_cap - new_flow;
        _re.cap = new_flow;
    }

    Cap flow(int s, int t)
    {
        return flow(s, t, Cap.max);
    }

    Cap flow(int s, int t, Cap flow_limit)
    {
        import std.container : DList;
        import std.algorithm : min;

        assert(0 <= s && s < _n);
        assert(0 <= t && t < _n);
        assert(s != t);

        auto level = new int[](_n), iter = new int[](_n);
        DList!int que;

        void bfs()
        {
            level[] = -1;
            level[s] = 0;
            que.clear();
            que.insertBack(s);
            while (!que.empty)
            {
                int v = que.front;
                que.removeFront();
                foreach (e; g[v])
                {
                    if (e.cap == 0 || level[e.to] >= 0)
                        continue;
                    level[e.to] = level[v] + 1;
                    if (e.to == t)
                        return;
                    que.insertBack(e.to);
                }
            }
        }

        Cap dfs(int v, Cap up)
        {
            if (v == s)
                return up;
            Cap res = 0;
            int level_v = level[v];
            for (; iter[v] < cast(int)(g[v].length); iter[v]++)
            {
                auto i = iter[v];
                auto e = g[v][i];
                if (level_v <= level[e.to] || g[e.to][e.rev].cap == 0)
                    continue;
                Cap d = dfs(e.to, min(up - res, g[e.to][e.rev].cap));
                if (d <= 0)
                    continue;
                g[v][i].cap += d;
                g[e.to][e.rev].cap -= d;
                res += d;
                if (res == up)
                    break;
            }
            return res;
        }

        Cap flow = 0;
        while (flow < flow_limit)
        {
            bfs();
            if (level[t] == -1)
                break;
            iter[] = 0;
            while (flow < flow_limit)
            {
                Cap f = dfs(t, flow_limit - flow);
                if (!f)
                    break;
                flow += f;
            }
        }
        return flow;
    }

    bool[] minCut(int s)
    {
        import std.container : DList;

        auto visited = new bool[](_n);
        DList!int que;
        que.insertBack(s);
        while (!que.empty)
        {
            int p = que.front;
            que.removeFront();
            visited[p] = true;
            foreach (e; g[p])
            {
                if (e.cap && !visited[e.to])
                {
                    visited[e.to] = true;
                    que.insertBack(e.to);
                }
            }
        }
        return visited;
    }

private:
    struct _edge
    {
        int to, rev;
        Cap cap;
    }

    int _n;
    Tuple!(int, int)[] pos;
    _edge[][] g;
}
// --- string ---

int[] saNaive(const ref int[] s) @safe pure nothrow
{
    import std.range : iota, array;
    import std.algorithm : sort;

    int n = cast(int) s.length;
    auto sa = iota(n).array;
    bool less(int l, int r)
    {
        if (l == r)
            return false;
        while (l < n && r < n)
        {
            if (s[l] != s[r])
                return s[l] < s[r];
            l++;
            r++;
        }
        return l == n;
    }

    sort!(less)(sa);
    return sa;
}

int[] saDoubling(const ref int[] s) @safe pure nothrow
{
    import std.range : iota, array;
    import std.algorithm : sort, swap;

    int n = cast(int) s.length;
    auto sa = iota(n).array;
    auto rnk = s.dup;
    auto tmp = new int[](n);

    for (int k = 1; k < n; k *= 2)
    {
        bool less(int x, int y)
        {
            if (rnk[x] != rnk[y])
                return rnk[x] < rnk[y];
            int rx = x + k < n ? rnk[x + k] : -1;
            int ry = y + k < n ? rnk[y + k] : -1;
            return rx < ry;
        }

        sort!(less)(sa);
        tmp[sa[0]] = 0;
        foreach (i; 1 .. n)
            tmp[sa[i]] = tmp[sa[i - 1]] + (less(sa[i - 1], sa[i]) ? 1 : 0);
        swap(tmp, rnk);
    }
    return sa;
}

int[] saIs(int THRESHOLD_NAIVE = 10, int THRESHOLD_DOUBLING = 40)(int[] s, int upper)
{
    int n = cast(int) s.length;
    if (n == 0)
        return [];
    if (n == 1)
        return [0];
    if (n == 2)
    {
        if (s[0] < s[1])
        {
            return [0, 1];
        }
        else
        {
            return [1, 0];
        }
    }
    if (n < THRESHOLD_NAIVE)
        return saNaive(s);
    if (n < THRESHOLD_DOUBLING)
        return saDoubling(s);
    auto sa = new int[](n);
    auto ls = new bool[](n);
    foreach_reverse (i; 0 .. n - 2 + 1)
        ls[i] = (s[i] == s[i + 1]) ? ls[i + 1] : (s[i] < s[i + 1]);
    auto sum_l = new int[](upper + 1);
    auto sum_s = new int[](upper + 1);
    foreach (i; 0 .. n)
    {
        if (!ls[i])
        {
            sum_s[s[i]]++;
        }
        else
        {
            sum_l[s[i] + 1]++;
        }
    }
    foreach (i; 0 .. upper + 1)
    {
        sum_s[i] += sum_l[i];
        if (i < upper)
            sum_l[i + 1] += sum_s[i];
    }
    void induce(const ref int[] lms)
    {
        sa[] = -1;
        auto buf = new int[](upper + 1);
        buf[] = sum_s[];
        foreach (d; lms)
        {
            if (d == n)
                continue;
            sa[buf[s[d]]++] = d;
        }
        buf[] = sum_l[];
        sa[buf[s[n - 1]]++] = n - 1;
        foreach (i; 0 .. n)
        {
            int v = sa[i];
            if (1 <= v && !ls[v - 1])
                sa[buf[s[v - 1]]++] = v - 1;
        }
        buf[] = sum_l[];
        foreach_reverse (i; 0 .. n)
        {
            int v = sa[i];
            if (v >= 1 && ls[v - 1])
            {
                sa[--buf[s[v - 1] + 1]] = v - 1;
            }
        }
    }

    auto lms_map = new int[](n + 1);
    lms_map[] = -1;
    int m = 0;
    foreach (i; 1 .. n)
        if (!ls[i - 1] && ls[i])
            lms_map[i] = m++;
    int[] lms;
    lms.reserve(m);
    foreach (i; 1 .. n)
        if (!ls[i - 1] && ls[i])
            lms ~= i;

    induce(lms);

    if (m)
    {
        int[] sorted_lms;
        sorted_lms.reserve(m);
        foreach (int v; sa)
            if (lms_map[v] != -1)
                sorted_lms ~= v;
        auto rec_s = new int[](m);
        int rec_upper = 0;
        rec_s[lms_map[sorted_lms[0]]] = 0;
        foreach (i; 1 .. m)
        {
            int l = sorted_lms[i - 1];
            int r = sorted_lms[i];
            int end_l = (lms_map[l] + 1 < m) ? lms[lms_map[l] + 1] : n;
            int end_r = (lms_map[r] + 1 < m) ? lms[lms_map[r] + 1] : n;
            bool same = true;
            if (end_l - l != end_r - r)
            {
                same = false;
            }
            else
            {
                while (l < end_l)
                {
                    if (s[l] != s[r])
                        break;
                    l++;
                    r++;
                }
                if (l == n || s[l] != s[r])
                    same = false;
            }
            if (!same)
                rec_upper++;
            rec_s[lms_map[sorted_lms[i]]] = rec_upper;
        }
        auto rec_sa = saIs!(THRESHOLD_NAIVE, THRESHOLD_DOUBLING)(rec_s, rec_upper);
        foreach (i; 0 .. m)
            sorted_lms[i] = lms[rec_sa[i]];
        induce(sorted_lms);
    }
    return sa;
}

int[] suffixArray(int[] s, int upper) @safe pure nothrow
{
    assert(0 <= upper);
    foreach (int d; s)
        assert(0 <= d && d <= upper);
    auto sa = saIs(s, upper);
    return sa;
}

int[] suffixArray(T)(T[] s)
{
    import std.range : iota;
    import std.array : array;
    import std.algorithm : sort;

    int n = cast(int) s.length;
    int[] idx = iota(n).array;
    sort!((int l, int r) => s[l] < s[r])(idx);
    auto s2 = new int[](n);
    int now = 0;
    foreach (i; 0 .. n)
    {
        if (i && s[idx[i - 1]] != s[idx[i]])
            now++;
        s2[idx[i]] = now;
    }
    return saIs(s2, now);
}

int[] suffixArray(string s) @safe pure nothrow
{
    int n = cast(int) s.length;
    auto s2 = new int[](n);
    foreach (i; 0 .. n)
        s2[i] = s[i];
    return saIs(s2, 255);
}

int[] lcpArray(T)(T[] s, int[] sa)
{
    int n = cast(int) s.length;
    assert(n >= 1);
    auto rnk = new int[](n);
    foreach (i; 0 .. n)
        rnk[sa[i]] = i;
    auto lcp = new int[](n - 1);
    int h = 0;
    foreach (i; 0 .. n)
    {
        if (h > 0)
            h--;
        if (rnk[i] == 0)
            continue;
        int j = sa[rnk[i] - 1];
        for (; j + h < n && i + h < n; h++)
            if (s[j + h] != s[i + h])
                break;
        lcp[rnk[i] - 1] = h;
    }
    return lcp;
}

int[] lcpArray(string s, int[] sa) @safe pure nothrow
{
    int n = cast(int) s.length;
    auto s2 = new int[](n);
    foreach (i; 0 .. n)
        s2[i] = s[i];
    return lcpArray(s2, sa);
}

int[] zAlgorithm(T)(T[] s)
{
    import std.algorithm : min;

    int n = cast(int) s.length;
    if (n == 0)
        return [];
    auto z = new int[](n);
    int j;
    foreach (i; 1 .. n)
    {
        z[i] = (j + z[j] < i) ? 0 : min(j + z[j] - i, z[i - j]);
        while (i + z[i] < n && s[z[i]] == s[i + z[i]])
            z[i]++;
        if (j + z[j] < i + z[i])
            j = i;
    }
    z[0] = n;
    return z;
}

int[] zAlgorithm(string s) @safe pure nothrow
{
    int n = cast(int) s.length;
    auto s2 = new int[](n);
    foreach (i; 0 .. n)
    {
        s2[i] = s[i];
    }
    return zAlgorithm(s2);
}
// --- twosat ---

struct TwoSat
{
public:
    this(int n) @safe nothrow
    {
        _n = n;
        _answer = new bool[](n);
        scc = SccGraphImpl(2 * n + 2);
    }

    void addClause(int i, bool f, int j, bool g) @safe nothrow
    {
        assert(0 <= i && i < _n);
        assert(0 <= j && j < _n);
        scc.addEdge(2 * i + (f ? 0 : 1), 2 * j + (g ? 1 : 0));
        scc.addEdge(2 * j + (g ? 0 : 1), 2 * i + (f ? 1 : 0));
    }

    bool satisfiable() @safe nothrow
    {
        auto id = scc.sccIds()[1];
        foreach (i; 0 .. _n)
        {
            if (id[2 * i] == id[2 * i + 1])
                return false;
            _answer[i] = id[2 * i] < id[2 * i + 1];
        }
        return true;
    }

    bool[] answer() @safe nothrow @nogc
    {
        return _answer;
    }

private:
    int _n;
    bool[] _answer;
    SccGraphImpl scc;
}
// --- dsu ---

struct Dsu
{
public:
    this(long n) @safe nothrow
    {
        _n = cast(int) n, parent_or_size = new int[](n);
        parent_or_size[] = -1;
    }

    int merge(long a, long b) @safe nothrow @nogc
    {
        assert(0 <= a && a < _n);
        assert(0 <= b && b < _n);
        int x = leader(a), y = leader(b);
        if (x == y)
            return x;
        if (-parent_or_size[x] < -parent_or_size[y])
        {
            auto tmp = x;
            x = y;
            y = tmp;
        }
        parent_or_size[x] += parent_or_size[y];
        parent_or_size[y] = x;
        return x;
    }

    bool same(long a, long b) @safe nothrow @nogc
    {
        assert(0 <= a && a < _n);
        assert(0 <= b && b < _n);
        return leader(a) == leader(b);
    }

    int leader(long a) @safe nothrow @nogc
    {
        assert(0 <= a && a < _n);
        if (parent_or_size[a] < 0)
            return cast(int) a;
        return parent_or_size[a] = leader(parent_or_size[a]);
    }

    int size(long a) @safe nothrow @nogc
    {
        assert(0 <= a && a < _n);
        return -parent_or_size[leader(a)];
    }

    int[][] groups() @safe nothrow
    {
        auto leader_buf = new int[](_n), group_size = new int[](_n);
        foreach (i; 0 .. _n)
        {
            leader_buf[i] = leader(i);
            group_size[leader_buf[i]]++;
        }
        auto result = new int[][](_n);
        foreach (i; 0 .. _n)
            result[i].reserve(group_size[i]);
        foreach (i; 0 .. _n)
            result[leader_buf[i]] ~= i;
        int[][] filtered;
        foreach (r; result)
            if (r.length != 0)
                filtered ~= r;
        return filtered;
    }

private:
    int _n;
    int[] parent_or_size;
}
// --- modint ---

struct StaticModInt(int m) if (1 <= m)
{
    import std.traits : isSigned, isUnsigned, isSomeChar;

    alias mint = StaticModInt;
public:
    static int mod()
    {
        return m;
    }

    static mint raw(int v)
    {
        mint x;
        x._v = v;
        return x;
    }

    this(T)(T v) if (isSigned!T)
    {
        long x = cast(long)(v % cast(long)(umod()));
        if (x < 0)
            x += umod();
        _v = cast(uint)(x);
    }

    this(T)(T v) if (isUnsigned!T || isSomeChar!T)
    {
        _v = cast(uint)(v % umod());
    }

    this(bool v)
    {
        _v = cast(uint)(v) % umod();
    }

    auto opAssign(T)(T v)
            if (isSigned!T || isUnsigned!T || isSomeChar!T || is(T == bool))
    {
        return this = mint(v);
    }

    inout uint val() pure
    {
        return _v;
    }

    ref mint opUnary(string op)() pure nothrow @safe if (op == "++")
    {
        _v++;
        if (_v == umod())
            _v = 0;
        return this;
    }

    ref mint opUnary(string op)() pure nothrow @safe if (op == "--")
    {
        if (_v == 0)
            _v = umod();
        _v--;
        return this;
    }

    mint opUnary(string op)() if (op == "+" || op == "-")
    {
        mint x;
        return mixin("x " ~ op ~ " this");
    }

    ref mint opOpAssign(string op, T)(T value) if (!is(T == mint))
    {
        mint y = value;
        return opOpAssign!(op)(y);
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "+" && is(T == mint))
    {
        _v += value._v;
        if (_v >= umod())
            _v -= umod();
        return this;
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "-" && is(T == mint))
    {
        _v -= value._v;
        if (_v >= umod())
            _v += umod();
        return this;
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "*" && is(T == mint))
    {
        ulong z = _v;
        z *= value._v;
        _v = cast(uint)(z % umod());
        return this;
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "/" && is(T == mint))
    {
        return this = this * value.inv();
    }

    mint pow(long n) const pure
    {
        assert(0 <= n);
        mint x = this, r = 1;
        while (n)
        {
            if (n & 1)
                r *= x;
            x *= x;
            n >>= 1;
        }
        return r;
    }

    mint inv() const pure
    {
        static if (prime)
        {
            assert(_v);
            return pow(umod() - 2);
        }
        else
        {
            auto eg = invGcd(_v, mod());
            assert(eg[0] == 1);
            return mint(eg[1]);
        }
    }

    mint opBinary(string op, R)(const R value) const pure 
            if (op == "+" || op == "-" || op == "*" || op == "/")
    {
        static if (is(R == mint))
        {
            mint x;
            x += this;
            return x.opOpAssign!(op)(value);
        }
        else
        {
            mint y = value;
            return opOpAssign!(op)(y);
        }
    }

    mint opBinaryRight(string op, L)(const L value) const if (!is(L == mint))
    {
        mint y = value;
        return y.opBinary!(op)(this);
    }

    bool opEquals(R)(const R value) const
    {
        static if (is(R == mint))
        {
            return _v == value._v;
        }
        else
        {
            mint y = mint(value);
            return this == y;
        }
    }

private:
    uint _v;
    uint umod() pure const
    {
        return m;
    }

    enum bool prime = isPrime!(m);
}

struct DynamicModInt(int id)
{
    import std.traits : isSigned, isUnsigned, isSomeChar;

    alias mint = DynamicModInt;
public:
    static int mod()
    {
        return bt.umod();
    }

    static void setMod(int m)
    {
        assert(1 <= m);
        bt = Barrett(m);
    }

    static mint raw(int v)
    {
        mint x;
        x._v = v;
        return x;
    }

    this(T)(T v) if (isSigned!T)
    {
        long x = cast(long)(v % cast(long)(umod()));
        if (x < 0)
            x += umod();
        _v = cast(uint)(x);
    }

    this(T)(T v) if (isUnsigned!T || isSomeChar!T)
    {
        _v = cast(uint)(v % umod());
    }

    this(bool v)
    {
        _v = cast(uint)(v) % umod();
    }

    auto opAssign(T)(T v)
            if (isSigned!T || isUnsigned!T || isSomeChar!T || is(T == bool))
    {
        return this = mint(v);
    }

    inout uint val()
    {
        return _v;
    }

    ref mint opUnary(string op)() nothrow @safe if (op == "++")
    {
        _v++;
        if (_v == umod())
            _v = 0;
        return this;
    }

    ref mint opUnary(string op)() nothrow @safe if (op == "--")
    {
        if (_v == 0)
            _v = umod();
        _v--;
        return this;
    }

    mint opUnary(string op)() if (op == "+" || op == "-")
    {
        mint x;
        return mixin("x " ~ op ~ " this");
    }

    ref mint opOpAssign(string op, T)(T value) if (!is(T == mint))
    {
        mint y = value;
        return opOpAssign!(op)(y);
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "+" && is(T == mint))
    {
        _v += value._v;
        if (_v >= umod())
            _v -= umod();
        return this;
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "-" && is(T == mint))
    {
        _v -= value._v;
        if (_v >= umod())
            _v += umod();
        return this;
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "*" && is(T == mint))
    {
        _v = bt.mul(_v, value._v);
        return this;
    }

    ref mint opOpAssign(string op, T)(T value) if (op == "/" && is(T == mint))
    {
        return this = this * value.inv();
    }

    mint pow(long n) const
    {
        assert(0 <= n);
        mint x = this, r = 1;
        while (n)
        {
            if (n & 1)
                r *= x;
            x *= x;
            n >>= 1;
        }
        return r;
    }

    mint inv() const
    {
        auto eg = invGcd(_v, mod());
        assert(eg[0] == 1);
        return mint(eg[1]);
    }

    mint opBinary(string op, R)(const R value)
            if (op == "+" || op == "-" || op == "*" || op == "/")
    {
        static if (is(R == mint))
        {
            mint x;
            x += this;
            return x.opOpAssign!(op)(value);
        }
        else
        {
            mint y = value;
            return opOpAssign!(op)(y);
        }
    }

    mint opBinaryRight(string op, L)(const L value) const if (!is(L == mint))
    {
        mint y = value;
        return y.opBinary!(op)(this);
    }

    bool opEquals(R)(const R value) const
    {
        static if (is(R == mint))
        {
            return _v == value._v;
        }
        else
        {
            mint y = mint(value);
            return this == y;
        }
    }

private:
    uint _v;
    static Barrett bt = Barrett(998_244_353);
    uint umod()
    {
        return bt.umod();
    }
}

alias modint998244353 = StaticModInt!(998244353);
alias modint1000000007 = StaticModInt!(1000000007);
alias modint = DynamicModInt!(-1);
