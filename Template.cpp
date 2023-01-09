#include <bits/stdc++.h>
#pragma GCC optimize("O2")
using namespace std;

#define mk make_pair
#define mt make_tuple
#define all(A) A.begin(), A.end()
#define sz(A) int(A.size())

template <class T, class T2>
inline int chkmin(T &a, T2 b)
{
    return a > b ? a = b, 1 : 0;
}
template <class T, class T2>
inline int chkmax(T &a, T2 b) { return a < b ? a = b, 1 : 0; }
template <class T, class T2>
inline T mmin(T a, T2 b) { return a < b ? a : b; }
template <class T, class T2>
inline T mmax(T a, T2 b) { return a > b ? a : b; }
template <class T, class T2>
inline void srt(T &a, T2 &b)
{
    if (a > b)
        swap(a, b);
}
template <class T>
inline T aabs(T a) { return a < 0 ? -a : a; }
template <class T, class... T2>
inline T mmin(T a, T2... b) { return mmin(a, mmin(b...)); }
template <class T, class... T2>
inline T mmax(T a, T2... b) { return mmax(a, mmax(b...)); }
#define min mmin
#define max mmax
#define abs aabs

typedef long long ll;
typedef unsigned long long ull;
typedef pair<int, int> pii;
typedef pair<ll, int> pli;
typedef pair<ll, ll> pll;

template <class T>
using maxheap = priority_queue<T, vector<T>, less<T>>;
template <class T>
using minheap = priority_queue<T, vector<T>, greater<T>>;

const ll Mod1 = 1e9 + 7;
const ll Mod2 = 998244353;
ll Mod = Mod1;
const int Max = 1e6 + 10;
const int MAX = 1e6 + 10;
const int MaxSQ = 2e5 + 10;
const int SQ = 500;
const ll INF = 1LL * 1e18 + 10;
const int Inf = 1e9 + 7;
const int Log = 20;

#pragma region Combinatorics
struct mint;
mint inv(const mint &a);
mint pw(mint a, ll b);
struct mint
{
private:
    ll _val;

public:
    mint()
    {
        _val = 0;
    }
    mint(ll value)
    {
        _val = value % Mod;
    }
    mint(ll value, const bool &&ok)
    {
        _val = value;
    }

    inline mint operator+(mint b) const
    {
        b._val += this->_val;
        if (b._val > Mod)
            b._val -= Mod;
        return b;
    }
    inline mint operator-(mint b) const
    {
        b._val = this->_val + Mod - b._val;
        if (b._val > Mod)
            b._val -= Mod;
        return b;
    }
    inline mint operator*(mint b) const
    {
        b._val = b._val * this->_val % Mod;
        return b;
    }
    inline mint operator/(mint b) const
    {
        b._val = this->_val * inv(b)._val % Mod;
        return b;
    }

    inline mint &operator+=(const mint &b)
    {
        _val += b._val;
        if (_val > Mod)
            _val -= Mod;
        return *this;
    }
    inline mint &operator-=(const mint &b)
    {
        _val += Mod - b._val;
        if (_val > Mod)
            _val -= Mod;
        return *this;
    }
    inline mint &operator*=(const mint &b)
    {
        _val = _val * b._val % Mod;
        return *this;
    }
    inline mint &operator/=(const mint &b)
    {
        _val = _val * inv(b)._val % Mod;
        return *this;
    }

    mint &operator=(const mint &b)
    {
        _val = b._val;
        return *this;
    }

    explicit operator ll() const
    {
        return _val;
    }
    explicit operator bool() const
    {
        return _val;
    }
};

inline ostream &operator<<(ostream &stream, const mint &x)
{
    return stream << (ll)x;
}

inline mint pw(mint a, ll b)
{
    mint res = 1;
    while (b > 0)
    {
        if (b & 1)
            res *= a;
        a *= a;
        b >>= 1;
    }
    return res;
}

inline mint inv(const mint &a)
{
    return pw(a, Mod - 2);
}

mint fac[Max], ifac[Max];
inline void init_fac()
{
    if ((ll)fac[0])
        return;

    fac[0] = 1;
    ifac[0] = 1;
    for (ll i = 1; i < Max; i++)
        fac[i] = fac[i - 1] * mint(i), ifac[i] = inv(fac[i]);
}

inline mint Comb(const int &a, const int &b)
{
    return fac[b] / (fac[a] * fac[b - a]);
}

#pragma endregion

#pragma region NumberTheory
int lp[MAX];
inline void init_sieve()
{
    if (lp[2])
        return;

    for (int i = 2; i < MAX; i++)
        if (!lp[i])
            for (int j = i; j < MAX; j += i)
                lp[j] = i;
}
#pragma endregion

#pragma region GraphTheory

struct Tree
{
    int N;
    int *H, *Sz, *Sttime, *Edtime;
    int **Par;
    vector<int> *Adj;
    vector<int> *Ch;

    Tree(int n)
    {
        N = n;
        H = new int[n + 5];
        Sz = new int[n + 5];
        Sttime = new int[n + 5];
        Edtime = new int[n + 5];
        Adj = new vector<int>[n + 5];
        Ch = new vector<int>[n + 5];
        Par = new int *[n + 5];
        Par[0] = new int[(n + 5) * Log];
        for (int i = 1; i < n + 5; i++)
        {
            Par[i] = Par[i - 1] + Log;
        }
    }
    ~Tree()
    {
        delete[] H;
        delete[] Sz;
        delete[] Sttime;
        delete[] Edtime;

        delete[] Par[0];
        delete[] Par;

        delete[] Adj;
        delete[] Ch;
    }
    inline void Input1()
    {
        for (int i = 1; i < N; i++)
        {
            int a, b;
            cin >> a >> b;
            Adj[a].push_back(b);
            Adj[b].push_back(a);
        }
    }
    inline void Input2()
    {
        for (int i = 2; i <= N; i++)
        {
            int p;
            cin >> p;
            Adj[p].push_back(i);
            Adj[i].push_back(p);
        }
    }
    void MakeRooted(const int &v)
    {
        Sz[v] = 1;
        for (int lg = 1; lg < Log; lg++)
            Par[v][lg] = Par[Par[v][lg - 1]][lg - 1];
        for (int u : Adj[v])
            if (u != Par[v][0])
            {
                Ch[v].push_back(u);
                H[u] = H[v] + 1;
                Par[u][0] = v;
                Edtime[u] = Sttime[u] = Edtime[v] + 1;
                MakeRooted(u);
                Edtime[v] = Edtime[u];
                Sz[v] += Sz[u];
            }
    }
    inline int LCA(int a, int b)
    {
        if (a == b)
            return a;
        if (Sttime[a] > Sttime[b])
            swap(a, b);
        for (int lg = Log; lg--;)
            if (Sttime[a] < Sttime[Par[b][lg]])
                b = Par[b][lg];
        return Par[b][0];
    }
    inline int KthPar(int v, const int &k)
    {
        for (int lg = 0; lg < Log; lg++)
            if ((1 << lg) & k)
                v = Par[v][lg];
        return v;
    }
    inline bool IsPar(const int &p, const int &v)
    {
        return Sttime[p] <= Sttime[v] && Sttime[v] <= Edtime[p];
    }
    inline int Dist(const int &a, const int &b)
    {
        int l = LCA(a, b);
        return H[a] + H[b] - (H[l] << 1);
    }
};

#pragma endregion

#pragma region DataStructures

template <class num>
struct RMQ
{
    num **rmq;
    static int lg[MAX];
    RMQ(const int &N, const num *A)
    {
        // malloc
        rmq = new num *[N + 5];
        rmq[0] = new num[(N + 5) * Log];
        for (int i = 1; i < N + 5; i++)
            rmq[i] = rmq[i - 1] + Log;

        for (int i = 0; i <= N; i++)
            rmq[i][0] = A[i];
        for (int l = 1, p = 1; l < Log; l++, p <<= 1)
        {
            for (int i = 0; i <= N - p; i++)
            {
                rmq[i][l] = merge(rmq[i][l - 1], rmq[i + p][l - 1]);
            }
        }

        if (!lg[2])
        {
            cout << "ello" << endl;
            for (int i = 2; i < MAX; i++)
                lg[i] = lg[i >> 1] + 1;
        }
    }
    ~RMQ()
    {
        delete[] rmq[0];
        delete[] rmq;
    }
    num get(const int &l, const int &r)
    {
        int sz = 1 << lg[r - l];
        return merge(rmq[l][lg[sz]], rmq[r - sz][lg[sz]]);
    }
    inline num merge(const num &a, const num &b)
    {
        return max(a, b); // get max
    }
};
template <class num>
int RMQ<num>::lg[MAX];

template <class num>
struct FEN
{
    int n;
    num *bit;

    inline int mnbit(const int &x)
    {
        return x & -x;
    }
    FEN(const int &N)
    {
        n = N;
        bit = new int[n + 5];
    }
    FEN(const int &N, const num *A)
    {
        n = N;
        bit = new num[n + 5];
        for (int i = 1; i <= n; i++)
        {
            bit[i] += A[i];
            bit[i + mnbit(i)] += bit[i];
        }
    }
    ~FEN()
    {
        delete[] bit;
    }
    void upd(int i, const num &x)
    {
        for (; i <= n; i += mnbit(i))
        {
            bit[i] += x;
        }
    }
    num get(int i)
    {
        num res = 0;
        for (; i; i -= mnbit(i))
        {
            res += bit[i];
        }
        return res;
    }
};

template <class Node>
struct SEG
{
    int n;
    Node *node;

    SEG(const int &N)
    {
        n = N + 1;
        node = new Node[n << 1];

        int *null = NULL;
        for (int i = 0; i < n; i++)
            node[n + i] = Node(null);

        for (int i = n; i--;)
            Node::merge(node[i << 1], node[i << 1 | 1], node[i]);
    }
    template <class Ty>
    SEG(const int &N, const Ty *A)
    {
        n = N + 1;
        node = new Node[n << 1];

        for (int i = 0; i < n; i++)
            node[n + i] = Node(A + i);

        for (int i = n; i--;)
            Node::merge(node[i << 1], node[i << 1 | 1], node[i]);
    }
    ~SEG()
    {
        delete[] node;
    }

    template <class Ty>
    void upd(int i, const Ty &x)
    {
        i += n;
        node[i].upd(x);

        for (; i >>= 1;)
            Node::merge(node[i << 1], node[i << 1 | 1], node[i]);
    }
    void rangeact(int l, int r, void (*act)(Node *))
    {
        l += n, r += n;
        for (; l < r; l >>= 1, r >>= 1)
        {
            if (l & 1)
                act(&node[l++]);
            if (r & 1)
                act(&node[--r]);
        }
    }
    Node get(int l, int r)
    {
        l += n, r += n;
        Node lv, lvt, rv, rvt;
        Node *lres = &lv,
             *lres_t = &lvt;
        Node *rres = &rv,
             *rres_t = &rvt;
        for (; l < r; l >>= 1, r >>= 1)
        {
            if (l & 1)
                Node::merge(*lres, node[l++], *lres_t), swap(lres, lres_t);
            if (r & 1)
                Node::merge(node[--r], *rres, *rres_t), swap(rres, rres_t);
        }
        Node::merge(*lres, *rres, *lres_t);
        return *lres_t;
    }
};
template <class T>
struct AdditionNode
{
    T x = 0;
    AdditionNode() // null state
    {
    }
    template <class Ty>
    AdditionNode(Ty *X) // filled
    {
        if (X == NULL)
        {
            // default node
            return;
        }
        // inputed node
        x = *X;
    }

    template <class Ty>
    void upd(const Ty &u)
    {
        x += u;
    }
    static void merge(const AdditionNode<T> &a, const AdditionNode<T> &b, AdditionNode<T> &res)
    {
        res.x = a.x + b.x;
    }
};
#pragma endregion

// Template End

void solve();

int main()
{
    ios::sync_with_stdio(0);
    cin.tie(0);
    cout.tie(0);

    int q;
    cin >> q;
    while (q--)
    {
        solve();
    }
}

int A[Max], B[Max], C[Max];

void solve()
{
    int n;
    cin >> n;
    // init_fac();
    // init_sieve();
}