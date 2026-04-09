#include<bits/stdc++.h>
using namespace std;

int main(){

    int dp[100001][3];
    int n;
    cin >> n;
    vector<int> a, b, c;
    for(int i=0;i<n;i++){
        int auxa, auxb, auxc;
        cin >> auxa >> auxb >> auxc;
        a.push_back(auxa);
        b.push_back(auxb);
        c.push_back(auxc);
    }
    dp[0][0] = a[0];
    dp[0][1] = b[0];
    dp[0][2] = c[0];
    for(int i=1;i<n;i++){
        dp[i][0] = max(dp[i-1][1] , dp[i-1][2]) + a[i];
        dp[i][1] = max(dp[i-1][0] , dp[i-1][2]) + b[i];
        dp[i][2] = max(dp[i-1][1] , dp[i-1][0]) + c[i];
    }
    cout << max(max(dp[n-1][0], dp[n-1][1]), dp[n-1][2]);


    return 0;
}