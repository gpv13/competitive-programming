#include<bits/stdc++.h>
using namespace std;

int n;
vector<double> prob(2999);
vector<double> probInv(2999);
double memo[3001][3001]; //id
bool visited[3001][3001];
double solve(int id, int ch, int ct){
    if(id == n){
        if(ct >= ch) return 0;
        else return 1;
    }
    if(visited[id][ch]){
        return memo[id][ch];
    }

    double ans = 1;
    ans = prob[id] * solve(id+1, ch+1, ct) + probInv[id] * solve(id+1, ch, ct +1);

    visited[id][ch] = true;
    return memo[id][ch] = ans;
}

int main(){

    cin >> n;
    memset(visited, false, sizeof(visited));
    for(int i=0;i<n;i++){
        cin >> prob[i];
        probInv[i] = 1.0 - prob[i];
    }
    cout << fixed << setprecision(12);
    cout << solve(0,0,0) << endl;


    return 0;
}