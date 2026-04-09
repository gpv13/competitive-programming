#include <bits/stdc++.h>
using namespace std;

typedef long long ll;
const ll MOD = 1000000000;

int main() {
    ll n, k;
    cin >> n >> k;
    vector<ll> A(n+1, 0);

    for (ll i = 0; i < k; ++i)
        A[i] = 1;

    ll sum = k % MOD;
    for (ll i = k; i <= n; ++i) {
        A[i] = sum;
        sum = (sum + A[i] - A[i - k] + MOD) % MOD; // adiciona o novo e remove o antigo da janela
    }

    cout << A[n] << endl;
    return 0;
}
