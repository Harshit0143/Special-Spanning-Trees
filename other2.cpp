#include "bits/stdc++.h"

using namespace std;

#define ll long long
#define pb push_back
#define pob pop_back()
#define mp make_pair
#define pf push_front
#define pof pop_front()
#define mod 1000000007
#define add_m(a, b) (((a % mod) + (b % mod)) % mod)
#define sub_m(a, b) (((a % mod) - (b % mod) + mod) % mod)
#define mul_m(a, b) (((a % mod) * (b % mod)) % mod)

class disjoint_set
{
private:
    ll n;
    ll *par;
    ll *size;

public:
    disjoint_set(ll arr_siz)
    {
        this->n = arr_siz;
        par = new ll[n];
        size = new ll[n];
        for (ll i = 0; i < n; i++)
            par[i] = i, size[i] = 1;
    }
    ll findUPar(ll node)
    {
        stack<ll> st;
        while (par[node] != node) // we will update the parent for all nodes in the path
        {
            st.push(node);
            node = par[node];
        }
        while (!st.empty())
        {
            par[st.top()] = node;
            st.pop();
        }
        return node;
    }

    void unionBySize(ll u, ll v)
    {
        ll ulp_u = findUPar(u);
        ll ulp_v = findUPar(v);
        if (ulp_u == ulp_v)
            return;
        if (size[ulp_u] < size[ulp_v])
            swap(ulp_u, ulp_v);

        par[ulp_v] = ulp_u;
        size[ulp_u] += size[ulp_v];
    }
    ll ccds()
    {
        ll cnt = 0;
        for (ll i = 0; i < n; i++)
            if (par[i] == i)
                cnt++;
        return cnt;
    }
    bool same_cc(ll u, ll v)
    {
        return findUPar(u) == findUPar(v) ? true : false;
    }
};

class binary_lift // considers root as 0 by default
{
private:
    vector<long long> *up;
    vector<long long> *max_edge;
    long long *depth;
    long long n;
    long long LOG = 18;

public:
    binary_lift(const vector<vector<pair<ll, ll> > > &adj)
    {
        this->n = adj.size();
        this->depth = new ll[n];
        this->up = new vector<long long>[n];
        this->max_edge = new vector<long long>[n];
        for (ll i = 0; i < n; i++)
            up[i] = vector<ll>(0), max_edge[i] = vector<ll>(0);

        queue<pair<ll, ll> > q;
        ll curr = 0;
        q.push(make_pair(0, -1));
        q.push(make_pair(-1, -1));
        while (!q.empty())
        {

            ll ver = q.front().first, par = q.front().second; // up list of par is empty
            q.pop();
            if (ver == -1)
            {
                curr++;
                if (!q.empty())
                    q.push(make_pair(-1, -1));
                continue;
            }
            depth[ver] = curr;
            for (pair<ll, ll> p : adj[ver])
            {
                ll nbr = p.first, edge_wt = p.second;
                if (nbr == par)
                    continue;

                up[nbr].push_back(ver);
                max_edge[nbr].push_back(edge_wt);

                for (ll j = 1; j - 1 < up[up[nbr][j - 1]].size(); j++)
                {
                    up[nbr].push_back(up[up[nbr][j - 1]][j - 1]);
                    max_edge[nbr].push_back(max(max_edge[nbr][j - 1], max_edge[up[nbr][j - 1]][j - 1]));
                }
                q.push(make_pair(nbr, ver));
            }
        }
    }
    /*
    break 'k' ll o powers of '2' so
    */

    ll kth_ancestor(ll ver, ll k)
    {
        // how to reach the root??
        if (depth[ver] < k)
            return -1;

        for (ll i = LOG; i >= 0; i--)
        {
            if (((1ll << i) & k) == 0) // in the later case we need a smaller step
                continue;

            ver = up[ver][i]; // the problem with minnimm is that
            // we are overall not doing
        }
        return ver;
    }
    ll lca(ll u, ll v)
    {
        if (depth[u] < depth[v])
            swap(u, v);
        ll diff = depth[u] - depth[v];
        for (ll j = LOG; j >= 0; j--)
        {
            if ((1 << j) & diff)
            {
                u = up[u][j];
            }
        }
        if (u == v)
            return u;
        for (ll j = LOG; j >= 0; j--)
        {
            if (j < up[u].size() && j < up[v].size() && up[u][j] != up[v][j])
            {
                u = up[u][j];
                v = up[v][j];
            }
        }
        return up[u][0];
    }
    ll heaviest_edge(ll u, ll v)
    {
        if (depth[u] < depth[v])
            swap(u, v);
        ll heaviest = INT64_MIN;
        ll diff = depth[u] - depth[v];
        for (ll i = LOG; i >= 0; i--)
            if ((1 << i) & diff)
            {
                heaviest = max(heaviest, max_edge[u][i]);
                u = up[u][i];
            }
        if (u == v)
            return heaviest;
        for (ll i = LOG; i >= 0; i--)
            if (i < up[u].size() && i < up[v].size() && up[u][i] != up[v][i])
            {
                heaviest = max(heaviest, max_edge[u][i]);
                heaviest = max(heaviest, max_edge[v][i]);
                u = up[u][i], v = up[v][i];
            }
        return max(heaviest, max(max_edge[u][0], max_edge[v][0]));

        //  return heaviest;
    }

    ll distance(ll a, ll b)
    {
        return depth[a] + depth[b] - 2 * depth[lca(a, b)];
    }
};

ll spanningTree(vector<pair<pair<ll, ll>, pair<ll, ll> > > &edges, vector<bool> taken, vector<vector<pair<ll, ll> > > &tree)
{
    ll n = tree.size();
    disjoint_set *forest = new disjoint_set(n);

    ll sum = 0, cnt = 0;
    sort(edges.begin(), edges.end());
    for (pair<pair<ll, ll>, pair<ll, ll> > p : edges)
    {
        ll wt = p.first.first, id = p.first.second, u = p.second.first, v = p.second.second;

        if (!forest->same_cc(u, v))
        {
            taken[id] = true;
            forest->unionBySize(u, v);
            tree[u].push_back(make_pair(v, wt));
            tree[v].push_back(make_pair(u, wt));
            sum += wt;
            cnt++;
        }
        if (cnt == n - 1)
            break;
    }
    return sum;
}

signed main()
{
    freopen("output.txt", "w", stdout);
    freopen("input.txt", "r", stdin);

    ll n, m, u, v, w;
    cin >> n >> m;
    vector<vector<pair<ll, ll> > > tree(n);
    vector<pair<pair<ll, ll>, pair<ll, ll> > > edges;
    vector<bool> taken(m);
    for (ll i = 0; i < m; i++)
    {
        cin >> u >> v >> w;
        u--, v--;
        edges.push_back(make_pair(make_pair(w, i), make_pair(u, v)));
    }
    ll weight = spanningTree(edges, taken, tree);
 
    binary_lift *lift = new binary_lift(tree);
    vector<ll> ans(m);
    for (ll j = 0; j < m; j++)
    {
        ll i = edges[j].first.second;
        if (taken[i])
        {
            ans[i] = weight;
            continue;
        }
        u = edges[j].second.first, v = edges[j].second.second, w = edges[j].first.first;
        ans[i] = weight + w - lift->heaviest_edge(u, v);
    }
    for (ll c : ans)
        cout << c << "\n";

    fclose(stdout);
    fclose(stdin);
    return 0;
}