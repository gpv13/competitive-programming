#include<bits/stdc++.h>
using namespace std;

int main(){

    long long int n;
    cin >> n;
    vector<long long int> shows(n+1);
    vector<long long int> dp(n+1);
    for(long long int i=1;i<=n;i++){
        cin >> shows[i];
    }
    dp[0] = 0;
    dp[1] = shows[1];
    for(long long int i=2;i<=n;i++){
        dp[i] = max(dp[i-1], dp[i-2] + shows[i]);
    }
    cout << dp[n] << endl;


    return 0;
}