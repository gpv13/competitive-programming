#include<bits/stdc++.h>
using namespace std;

//INCOMPLETO


int main(){

    vector<vector<int>> memo(250001);
    memo[0].push_back(-1);
    int n, k;
    cin >> n >> k;
    vector<int> nums(n);
    for(int i=0;i<n;i++)cin >> nums[i];

    for(int i=1;i<memo.size();i++){
        // cout << "aa";
        for(int j=0;j<n;j++){
            // cout << "bb";
            if(nums[j] > i) continue;
            // cout << "cc";
            if((i - nums[j] >= 0) && !memo[i-nums[j]].empty()){
                memo[i].push_back(nums[j]);
            }
        }
    }
    // cout << "a";
    set<int> possiveis;
    stack<pair<int,int>> p; //indice, quanto vai pra tras
    for(auto m : memo[k]){
        p.push({k, m});
    }
    vector<bool> visited(250001,false);
    visited[k] = true;
    while(!p.empty()){
        // cout << "a";

        pair<int,int> q = p.top();
        p.pop();
        if(q.second == -1) continue;
        if((q.first - q.second >= 0) && !visited[q.first - q.second]){

            for(auto m : memo[q.first - q.second]){
                if(m!=-1) p.push({q.first-q.second, m});
            }

            visited[q.first - q.second] = true;
        }
        possiveis.insert(q.second);
    }


    cout << "memo\n";
    int conta = 0;
    for(int i=0;i<=k;i++){
        cout << conta++;
        for(auto m : memo[i]) cout << " " << m;
        cout<<endl;
    }
    cout << endl;

    cout << "possiveis\n";
    for(auto s : possiveis) cout << s << " ";
    cout << endl;

    vector<int> dp(k+1, 0);
    dp[0] = 1;
    for(int i=1;i<=k;i++){
        for(auto s : possiveis){
            if(s > i) continue;
            dp[i] = max(dp[i], dp[i-s]);
        }
    }
    vector<int> ans;
    for(int i=0;i<=k;i++){
        if(dp[i] != 0) ans.push_back(i);
    }

    for(int i=0;i<ans.size();i++){
        if(!i) cout << ans[i];
        else cout << " " << ans[i];
    }

    cout << endl;

    return 0;
}