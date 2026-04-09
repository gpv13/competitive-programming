#include<bits/stdc++.h>
using namespace std;

int main(){

    int n, w;
    cin >> n >> w;
    vector<int> pesos(n+1), valores(n+1);
    for(int i=0;i<n;i++){
        cin >> pesos[i] >> valores[i];
    }
    long long int dp[n+2][w+1];
    
    for(int i=0;i<=w;i++){
        dp[n][i] = 0;
    }
    for(int i=n-1;i>=0;i--){
        for(int j=w;j>=0;j--){
            dp[i][j] = dp[i+1][j];
            if(pesos[i] <= j) dp[i][j] = max(dp[i][j], valores[i] + dp[i+1][j-pesos[i]]);
        }
    }

    cout << dp[0][w] << endl;

    return 0;
}