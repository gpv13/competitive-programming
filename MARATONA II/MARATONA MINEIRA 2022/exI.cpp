#include<bits/stdc++.h>
using namespace std;

int main(){

    long long int n;
    cin >> n;
    vector<long long int> poderes(n+1);
    for(long long int i=1;i<=n;i++) cin >> poderes[i];

    long long int dp1[n+1],dp2[n+1];
    dp1[0] = 0;
    dp2[0] = 0;
    dp1[1] = max(0LL, poderes[1]);
    dp2[1] = 0;
    dp2[2] = max(0LL, poderes[2]);
    for(long long int i=2;i<n;i++){
        dp1[i] = max(dp1[i-1], dp1[i-2] + poderes[i]);
    }
    
    for(long long int i=3;i<=n;i++){
        dp2[i] = max(dp2[i-1], dp2[i-2] + poderes[i]);
    }

    // for(auto m : dp1) cout << m << " ";
    // cout << endl;
    // for(auto m : dp2) cout << m << " ";
    // cout << endl;
    cout << max(dp1[n-1], dp2[n]) << endl;

    return 0;
}