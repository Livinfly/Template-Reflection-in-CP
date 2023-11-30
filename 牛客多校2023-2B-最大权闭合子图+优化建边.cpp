// #pragma GCC optimize(2)

#include <bits/stdc++.h>

#define fi first
#define se second
#define mkp(x, y) make_pair((x), (y))
#define all(x) (x).begin(), (x).end()

using namespace std;

typedef long long LL;
typedef double db;
typedef pair<int, int> PII;

const int N = 1e4+10, NN = 200*N, M = 1e6+10;
const int INF = 0x3f3f3f3f;

int Nid, nid[NN<<2], vir[N];
int idx, h[NN], ne[NN], ver[NN], e[NN]; // LL? INF?
int n, m, S, T;
int d[NN], cur[NN];
int w[NN];

void add(int a, int b, int c) {
    ver[idx] = b, e[idx] = c, ne[idx] = h[a], h[a] = idx ++;
}
void addFlow(int a, int b, int c1, int c2) {
    add(a, b, c1), add(b, a, c2);
}
bool bfs() {
    queue<int> q;
    memset(d, -1, sizeof d);
    q.push(S);
    d[S] = 0, cur[S] = h[S];
    while(q.size()) {
        int t = q.front(); q.pop();
        for(int i = h[t]; ~i; i = ne[i]) {
            int v = ver[i];
            if(d[v] == -1 && e[i]) {
                d[v] = d[t]+1;
                cur[v] = h[v];
                if(v == T) return true;
                q.push(v);
            }
        }
    }
    return false;
}
int update(int u, int limit) {
    if(u == T) return limit;
    int flow = 0;
    for(int i = cur[u]; ~i && flow < limit; i = ne[i]) {
        cur[u] = i;
        int v = ver[i];
        if(d[v] == d[u]+1 && e[i]) {
            int t = update(v, min(e[i], limit-flow));
            if(!t) d[v] = -1;
            flow += t;
            e[i] -= t;
            e[i^1] += t;
        }
    }
    return flow;
}
int dinic() { // LL?
    int res = 0, flow;
    while(bfs()) 
        while(flow = update(S, INF))
            res += flow;
    return res;
}

struct Info {
    int l, r;
};
struct SegmentTree {
    Info tr[NN<<2];
    // 0 - in fa->son, 1 - out son->fa 
    // ori out->in, add in->x->out
    vector<int> ve;
    #define ls(u) ((u)<<1)
    #define rs(u) ((u)<<1|1)
    void build(int u, int l, int r) {
        nid[u] = ++Nid;
        tr[u] = {l, r};
        if(l == r) {
            addFlow(nid[u], r, INF, 0); // 线段树本身对应的下标是 dfni
            return;
        }
        int mid = l+r >> 1;
        build(ls(u), l, mid), build(rs(u), mid+1, r);
        addFlow(nid[u], nid[ls(u)], INF, 0);
        addFlow(nid[u], nid[rs(u)], INF, 0);
    }
    void ask(int u, int l, int r) {
        assert(l <= r);
        auto [ll, rr] = tr[u];
        if(rr < l || r < ll) return;
        if(l <= ll && rr <= r) {
            ve.push_back(nid[u]);
            return;
        }
        ask(ls(u), l, r), ask(rs(u), l, r);
    }
    void addx2lr(int from, int l, int r, int c) {
        ve = vector<int>();
        ask(1, l, r);
        for(auto v: ve) addFlow(from, v, c, 0);
    }
    #undef ls
    #undef rs
}sgt;
struct HeavyLightDecompotion {
    int n, tms;
    vector<int> siz, top, dep, fa, dfni, dfno, rnk;
    vector<vector<int>> e;

    void init(int n) {
        this->n = n;
        siz.resize(n+1);
        top.resize(n+1);
        dep.resize(n+1);
        fa.resize(n+1);
        dfni.resize(n+1);
        dfno.resize(n+1);
        rnk.resize(n+1);
        tms = 0;
        e.assign(n+1, {});
    }
    void addEdge(int u, int v) {
        e[u].push_back(v);
        e[v].push_back(u);
    }
    void build(int root = 1) {
        top[root] = root;
        dep[root] = 1;
        fa[root] = -1; // 不要直接访问fa[i]...
        dfs1(root);
        dfs2(root);
    }
    void dfs1(int u) {
        if (fa[u] != -1) {
            e[u].erase(find(all(e[u]), fa[u]));
        }
        siz[u] = 1;
        for (auto &v : e[u]) {
            fa[v] = u;
            dep[v] = dep[u] + 1;
            dfs1(v);
            siz[u] += siz[v];
            if (siz[v] > siz[e[u][0]]) {
                swap(v, e[u][0]); // 保留引用
            }
        }
    }
    void dfs2(int u) {
        dfni[u] = ++tms;
        rnk[dfni[u]] = u;
        for (auto v : e[u]) {
            top[v] = (v == e[u][0]) ? top[u] : v;
            dfs2(v);
        }
        dfno[u] = tms+1;
    }
    void prefix() {
        for(int i = 1; i <= n; i ++) { // 在流里面已经是以dfni为标。
            vir[i] = ++Nid;
            addFlow(vir[i], dfni[i], INF, 0);
        }
        for(int i = 1; i <= n; i ++) {
            if(i != top[i] && fa[i] != -1) {
                addFlow(vir[i], vir[fa[i]], INF, 0);
            }
        }
    }
    int lca(int u, int v) {
        while (top[u] != top[v]) {
            if (dep[top[u]] > dep[top[v]]) {
                u = fa[top[u]];
            }
            else {
                v = fa[top[v]];
            }
        }
        return (dep[u] < dep[v]) ? u : v;
    }
    int getDist(int u, int v) {
        return dep[u] + dep[v] - 2 * dep[lca(u, v)];
    }
    int jump(int u, int k) {
        if (dep[u] < k) {
            return -1;
        }
        int d = dep[u] - k;
        while (dep[top[u]] > d) {
            u = fa[top[u]];
        }
        return rnk[dfni[u] - dep[u] + d];
    }
    void addEdge_x2y(int u, int x, int y, int c) {
        while(top[x] != top[y]) {
            if(dep[top[x]] < dep[top[y]]) swap(x, y);

            sgt.addx2lr(u, dfni[top[x]], dfni[x], c);
            // addFlow(u, vir[x], c, 0);
            x = fa[top[x]];
        }
        if(dep[x] < dep[y]) swap(x, y);
        if(x != y) sgt.addx2lr(u, dfni[y]+1, dfni[x], c);
    }
}hld;

void solve() {
    idx = 0, memset(h, -1, sizeof h);
    cin >> n >> m;
    S = NN-2, T = NN-1, Nid = n;
    hld.init(n);
    vector<array<int, 3>> rec(n);
    for(int i = 1; i < n; i ++) {
        auto &[u, v, c] = rec[i];
        cin >> u >> v >> c;
        hld.addEdge(u, v);
    }
    hld.build();
    // hld.prefix(); 链优化 - 可以优化一个log
    for(int i = 1; i <= n; i++) {
        nid[i] = hld.dfni[i];
    }
    for(int i = 1; i < n; i++) {
        auto [u, v, c] = rec[i];
        if(hld.dep[u] > hld.dep[v]) {
            // w[nid[u]] = c;
            addFlow(nid[u], T, c, 0);
        }
        else {
            // w[nid[v]] = c;
            addFlow(nid[v], T, c, 0);
        }
    }
    sgt.build(1, 1, n);
    int ans = 0;
    while(m--) {
        int a, b, x, y;
        cin >> a >> b >> x >> y;
        x -= y;
        if(x > 0) {
            Nid++;
            ans += x;
            addFlow(S, Nid, x, 0);
            hld.addEdge_x2y(Nid, a, b, INF);
        }
    }
    // cerr << dinic() << '\n';
    ans -= dinic();
    cout << ans << '\n';
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout << fixed;  // << setprecision(20); // double
    // freopen("i.txt", "r", stdin);
    // freopen("o.txt", "w", stdout);
    // time_t t1 = clock();
    int Tcase = 1;
    // cin >> Tcase; // scanf("%d", &Tcase);
    while (Tcase--) 
        solve();
    // cout << "time: " << 1000.0 * ((clock() - t1) / CLOCKS_PER_SEC) << "ms\n";
    return 0;
}