T[U] factorize(T = long, U = long)(T x)
{
    assert(0 < x, "x is negative");
    long[long] ps;
    while ((x & 1) == 0)
        x /= 2, ps[2] = (2 in ps) ? ps[2] + 1 : 1;
    for (long i = 3; i * i <= x; i += 2)
        while (x % i == 0)
            x /= i, ps[i] = (i in ps) ? ps[i] + 1 : 1;
    if (x != 1)
        ps[x] = (x in ps) ? ps[x] + 1 : 1;
    return ps;
}

T[] factorize(T = long)(T x)
{
    assert(0 < x, "x is negative");
    T[] result;
    while ((x & 1) == 0)
        x /= 2, result ~= 2;
    for (T i = 3; i * i <= x; i += 2)
        while (x % i == 0)
            x /= i, result ~= i;
    if (x != 1)
        result ~= x;
    return result;
}

T lcm(T)(T a, T b)
{
    return (a * b) / gcd(a, b);
}

/// x^^n % m
T powmod(T = long)(T x, T n, T m = 10 ^^ 9 + 7)
{
    if (n < 1)
        return 1;
    if (n & 1)
    {
        return x * powmod(x, n - 1, m) % m;
    }
    T tmp = powmod(x, n / 2, m);
    return tmp * tmp % m;
}

T invmod(T = long)(T x, T m = 10 ^^ 9 + 7)
{
    T powmod(T = long)(T x, T n, T m)
    {
        if (n < 1)
            return 1;
        if (n & 1)
        {
            return x * powmod(x, n - 1, m) % m;
        }
        T tmp = powmod(x, n / 2, m);
        return tmp * tmp % m;
    }

    return powmod(x, m - 2, m);
}

struct UnionFind
{
    alias T = long;
    T[] rank, parent, sizes;
    this(T n)
    {
        rank = new T[](n);
        sizes = new T[](n);
        sizes[] = 1;
        parent = iota!T(n).array();
    }

    T find(T x)
    {
        return (this.parent[x] == x) ? x : (this.parent[x] = this.find(this.parent[x]));
    }

    void unite(T x, T y)
    {
        T rx = this.find(x), ry = this.find(y);
        if (rx == ry)
            return;
        this.sizes[rx] = this.sizes[ry] = this.sizes[rx] + this.sizes[ry];
        if (this.rank[rx] == this.rank[ry])
            this.parent[rx] = ry, this.rank[ry]++;
        else if (this.rank[rx] < this.rank[ry])
            this.parent[rx] = ry;
        else
            this.parent[ry] = rx;
    }

    T size(T x)
    {
        return this.sizes[this.find(x)];
    }
}

/// Number of k-combinations
T combination(T = long)(T n, T k)
{
    assert(0 <= k);
    assert(0 <= n);
    if (n < k)
        return 0;
    k = min(n - k, k);
    if (k == 0)
        return 1;
    if (k == 1)
        return n;
    return memoize!combination(n - 1, k - 1) + memoize!combination(n - 1, k);
}

/// Number of k-combinations % m (precalculated)
alias Combination_mod = Combination_modImpl!long;
struct Combination_modImpl(T)
{
    T _n, _m;
    T[] _fact, _factinv;
    this(T maxnum, T mod = 10 ^^ 9 + 7)
    {
        _n = maxnum, _m = mod, _fact = new T[](_n + 1), _factinv = new T[](_n + 1), _fact[0] = 1;
        foreach (i; 1 .. _n + 1)
            _fact[i] = _fact[i - 1] * i % _m;
        T powmod(T x, T n, T m)
        {
            if (n < 1)
                return 1;
            if (n & 1)
            {
                return x * powmod(x, n - 1, m) % m;
            }
            T tmp = powmod(x, n / 2, m);
            return tmp * tmp % m;
        }

        foreach (i; 0 .. _n + 1)
            _factinv[i] = powmod(_fact[i], _m - 2, _m);
    }

    T opCall(T n, T k, T dummy = 10 ^^ 9 + 7)
    {
        return n < k ? 0 : ((_fact[n] * _factinv[n - k] % _m) * _factinv[k] % _m);
    }
}

/// BIT (1-indexed)
alias BinaryIndexedTree = BinaryIndexedTreeImpl!long;
struct BinaryIndexedTreeImpl(T)
{
    T[] _data;
    this(long n)
    {
        _data = new T[](n + 1);
    }

    T sum(long i)
    {
        T ans;
        for (; 0 < i; i -= (i & -i))
            ans += _data[i];
        return ans;
    }

    void add(long i, T x)
    {
        for (; i < _data.length; i += (i & -i))
            _data[i] += x;
    }
}
