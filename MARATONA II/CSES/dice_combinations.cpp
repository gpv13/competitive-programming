#include<bits/stdc++.h>
using namespace std;
#define MOD 1000000007
int main(){

    int n;
    cin >> n;
    long long int dp[n+1];
    memset(dp, 0, sizeof(dp));
    dp[0] = 1;
    for(int i=1;i<=n;i++){
        for(int j=1;j<=6;j++){
            if(j>i) break;
            dp[i] = (dp[i] + dp[i-j]) % MOD;
        }
    }
    // for(auto d: dp) cout << d << " ";
    cout << (dp[n])%MOD << endl;

    return 0;
}