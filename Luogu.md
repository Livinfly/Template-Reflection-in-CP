## 思路

前置知识：[三维偏序模板](https://www.luogu.com.cn/problem/P3810)

分析题意后，不难发现是可以交换三元组内顺序的三维偏序题。

相对于模板题，这题要求严格小于，我们一维一维来考虑。

第二维，在归并排序的过程中，注意先把 `<` 的部分，即可能有贡献的部分处理进去。

第三维，若有数据结构来维护，查询时，查区间减一即可。但后面发现，其实只需要把合法的部分的最小值直接处理出来就行。

最后是第一维，为了满足 `cdq分治` 左边都对右边可能有贡献的性质。

我们考虑预处理出每一段相同的数的最左端和最右端 `pl` 与 `pr`。

在取 `mid` 时，我们就找这样的分段点，这样左边的第一维都严格小于右边的第一维。

这样取的时候，会有边界问题，超出查询区间的左边界/右边界，在开始时要处理下这些情况。

## 代码

```cpp
#include <bits/stdc++.h>

#define fi first
#define se second
#define mkp(x, y) make_pair((x), (y))
#define all(x) (x).begin(), (x).end()

using namespace std;

typedef long long LL;
typedef pair<int, int> PII;

struct Node {
    int a, b, c;
};

const int N = 2e5+10, INF = 2e9;

int n, nn, k;
Node p[N], np[N], tmp[N];
map<int, int> pl, pr;

bool cmp1(const Node &a, const Node &b) {
    if(a.a == b.a) {
        if(a.b == b.b) {
            return a.c < b.c;
        }
        return a.b < b.b;
    }
    return a.a < b.a;
}
bool cdq(Node np[], int l, int r) {
    if(l >= r) return false;
    int mid = pl[np[l+r >> 1].a] - 1;
    if(mid < l) {
        mid = pr[np[l+r >> 1].a];
    }
    if(mid >= r) return false;
    if(cdq(np, l, mid) || cdq(np, mid+1, r)) {
        return true;
    }
    int i = l, j = mid+1, k = l;
    int t = INF;
    while(i <= mid && j <= r) {
        if(np[i].b < np[j].b) {
            t = min(t, np[i].c);
            tmp[k++] = np[i++];
        }
        else {
            if(t < np[j].c) {
                return true;
            }
            tmp[k++] = np[j++];
        }
    }
    while(j <= r) {
        if(t < np[j].c) {
            return true;
        }
        tmp[k++] = np[j++];
    }
    while(i <= mid) {
        tmp[k++] = np[i++];
    }
    for(int i = l; i <= r; i ++) {
        np[i] = tmp[i];
    }
    return false;
}
void solve() {
    cin >> n;
    for(int i = 0; i < n; i ++) {
        auto &[a, b, c] = p[i];
        cin >> a >> b >> c;
        if(a > b) swap(a, b);
        if(b > c) swap(b, c);
        if(a > b) swap(a, b);
    }
    sort(p, p+n, cmp1);
    for(int i = n-1; i >= 0; i --) {
        pl[p[i].a] = i;
    }
    for(int i = 0; i < n; i ++) {
        pr[p[i].a] = i;
    }
    bool ok = cdq(p, 0, n-1);
    if(ok) {
        cout << "Yes\n";
    }
    else {
        cout << "No\n";
    }
}
```

