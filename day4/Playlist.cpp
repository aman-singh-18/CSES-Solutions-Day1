#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;

typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> pbds;
typedef long long ll;
typedef vector<long long> vec;
typedef vector<vec> vec2;
typedef pair<ll, ll> pll;
typedef vector<pll> vecp;

vec presum(vec &nums)
{
    vec prefix(nums);
    for (ll i = 1; i < nums.size(); ++i)
        prefix[i] += prefix[i - 1];
    return prefix;
}

void print(vec v)
{
    for (ll i = 0; i < v.size(); i++)
    {
        cout << v[i] << " ";
    }
    cout << endl;
}

bool power_of_2(ll n) { return n > 0 && !(n & (n - 1)); }

ll power_of_2_count(ll n) { return n ? __builtin_ctz(n) : -1; }

bool is_prime(ll n)
{
    if (n < 2)
        return false;
    for (ll i = 2; i * i <= n; ++i)
        if (n % i == 0)
            return false;
    return true;
}

bool is_even(ll n)
{
    return !(n & 1);
}

void sort_vec(vec &v)
{
    sort(v.begin(), v.end());
}

void sort_reverse(vec &v)
{
    sort(v.begin(), v.end(), greater<ll>());
}

ll gcd(ll v, ll k) { return k ? gcd(k, v % k) : v; }

ll lcm(ll v, ll k) { return v / gcd(v, k) * k; }

ll sum_total(vec v)
{
    return accumulate(v.begin(), v.end(), 0LL);
}

ll max_in_array(vec v)
{
    return *max_element(v.begin(), v.end());
}

ll min_in_array(vec v)
{
    return *min_element(v.begin(), v.end());
}

bool is_present(const std::vector<ll> &v, ll target)
{
    return std::find(v.begin(), v.end(), target) != v.end();
}

ll count_ccurrences(const vector<ll> &vec, ll target)
{
    ll count = 0;
    for (ll num : vec)
    {
        if (num == target)
        {
            count++;
        }
    }
    return count;
}

ll leftmost_bit_pos(ll x)
{
    return 31 - __builtin_clz(x);
}

ll smallestPrimeDivisor(ll n)
{
    if (n % 2 == 0)
        return 2;
    for (ll i = 3; i * i <= n; i += 2)
        if (n % i == 0)
            return i;
    return n;
}

vec spf_vector(ll n)
{
    vec spf(n + 1);
    for (ll i = 2; i <= n; i++)
        spf[i] = i;
    for (ll i = 2; i * i <= n; i++)
    {
        if (spf[i] == i)
        {
            for (ll j = i * i; j <= n; j += i)
            {
                if (spf[j] == j)
                    spf[j] = i;
            }
        }
    }
    return spf;
}

map<ll, ll> prime_factorisation(ll n)
{
    map<ll, ll> factors;
    vec spf = spf_vector(n);
    while (n != 1)
    {
        factors[spf[n]]++;
        n /= spf[n];
    }
    return factors;
}

ll bit_count(ll x)
{
    return __builtin_popcount(x);
}

ll sqrt_binary_search(ll n)
{
    if (n < 2)
        return n; // 0 and 1 are their own square roots

    ll left = 1, right = n, ans = 0;
    while (left <= right)
    {
        ll mid = left + (right - left) / 2;
        if (mid <= n / mid)
        { // To avoid overflow: mid*mid <= n
            ans = mid;
            left = mid + 1;
        }
        else
        {
            right = mid - 1;
        }
    }
    return ans; // floor(sqrt(n))
}

map<ll, ll> pf(ll n)
{
    map<ll, ll> mp;

    for (ll i = 2; i * i <= n; i++)
    {
        while (n % i == 0)
        {
            mp[i]++;
            n /= i;
        }
    }

    if (n > 1)
    {
        mp[n]++;
    }

    return mp;
}

class disjointset
{
    vec rank, parent, size;

public:
    disjointset(ll n)
    { // this is v constructor
        rank.resize(n + 1, 0);
        parent.resize(n + 1);
        size.resize(n + 1, 1);
        for (ll i = 0; i <= n; i++)
            parent[i] = i;
    }
    // this is path compression for finding ultimate parent here we are doing  backtracking until we reach
    // to topmost node and also keep storing the thing which funtion is returning means ultimate parent
    ll findultimateparent(ll node)
    {
        if (node == parent[node])
            return node;
        return parent[node] = findultimateparent(parent[node]);
    }

    void unionbyrank(ll u, ll v)
    {
        ll ultimateparentofu = findultimateparent(u);
        ll ultimateparentofv = findultimateparent(v);
        if (ultimateparentofu == ultimateparentofv)
            return; // two nodes are already in same componet
        if (rank[ultimateparentofu] < rank[ultimateparentofv])
        {
            parent[ultimateparentofu] = ultimateparentofv;
        }
        else if (rank[ultimateparentofu] > rank[ultimateparentofv])
        {
            parent[ultimateparentofv] = ultimateparentofu;
        }
        else
        {
            parent[ultimateparentofv] = ultimateparentofu;
            rank[ultimateparentofu]++; // as larger one will grow in size
        }
    }

    void unionbysize(ll u, ll v)
    {
        ll ultimateparentofu = findultimateparent(u);
        ll ultimateparentofv = findultimateparent(v);
        if (ultimateparentofu == ultimateparentofv)
            return;
        if (size[ultimateparentofu] < size[ultimateparentofv])
        {
            parent[ultimateparentofu] = ultimateparentofv;
            size[ultimateparentofv] += size[ultimateparentofu];
        }
        else
        {
            parent[ultimateparentofv] = ultimateparentofu;
            size[ultimateparentofu] += size[ultimateparentofv];
        }
    }

    ll componentsize(ll idx)
    {
        return size[idx];
    }
};

ll countdigits(long long n)
{
    if (n == 0)
        return 1;
    ll count = 0;
    n = abs(n);
    while (n > 0)
    {
        n /= 10;
        count++;
    }
    return count;
}

void dfs(vec &visited, vec2 &adj, ll val, ll &cnt)
{
    visited[val] = 1;
    cnt++;
    for (auto now : adj[val])
    {
        if (!visited[now])
        {
            dfs(visited, adj, now, cnt);
        }
    }
}

int main()
{
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    {
        ll n;
        cin >> n;

        vec v(n);
        for (auto &val : v)
            cin >> val;

        map<ll, ll> m;
        vec prev(n, -1);
        for (int i = 0; i < n; i++)
        {
            if (m.find(v[i]) != m.end())
            {
                prev[i] = m[v[i]];
            }
            m[v[i]] = i;
        }
    
       
        vec anscnt(n,0);
        ll cnt = 1;
        anscnt[0] = 1;
        for (int i = 1; i < n; i++)
        {
            if (prev[i] == -1)
                cnt++;
            else
            {   
                cnt = min(i-prev[i],anscnt[i-1]+1);
            }
            anscnt[i] = cnt;
        }
        cout<<max_in_array(anscnt)<<endl;
    }
    return 0;
}
