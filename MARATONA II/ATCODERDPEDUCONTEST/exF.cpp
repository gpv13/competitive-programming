#include<bits/stdc++.h>
using namespace std;
int dp[3001][3001];
int main(){

    string s, t;
    cin >> s >> t;

    memset(dp, 0, sizeof(dp));

    if(s[0] == t[0]) dp[0][0] = 1;
    for(int i=1;i<s.size();i++){
            if(s[i] == t[0] || dp[i-1][0] == 1) dp[i][0] = 1;
    }
    for(int i=1;i<t.size();i++){
            if(s[0] == t[i] || dp[0][i-1] == 1) dp[0][i] = 1;
    }
    for(int i=1;i<s.size();i++){
        for(int j=1;j<t.size();j++){
            if(s[i] == t[j]) dp[i][j] = dp[i-1][j-1] + 1;
            else{
                dp[i][j] = max(dp[i-1][j], dp[i][j-1]);
            }
        }
    }
    int i = s.size()-1, j = t.size()-1;
    string reconstruc;
    //reconstrucao
    while(i>0 || j>0){
        if(j==0 || i==0){
            if(j>0){
                if(dp[i][j-1] != dp[i][j]){
                    reconstruc += s[i];
                }
                j--;
            }
            if(i>0){
                if(dp[i-1][j] != dp[i][j]){
                    reconstruc += s[i];
                }
                i--;
            }
        }
        else if(dp[i-1][j-1] != dp[i][j]) {
            reconstruc += s[i];
            i--; j--;
        }else{
            if(dp[i-1][j] > dp[i][j-1]) i--;
            else j--;
        }
    }
    if(dp[0][0] == 1){
        reconstruc += s[0];
    }
    reverse(reconstruc.begin(), reconstruc.end());
    cout << reconstruc << endl;

    return 0;
}