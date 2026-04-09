#include<bits/stdc++.h>
using namespace std;

//memo[idx][tightUpper][tightLower] -> {quant de sufixos dps, soma deles}
pair<long long, long long> memo[17][2][2];
bool visited[17][2][2];
string X, Y;
pair<long long,long long> solve(int idx, bool tightUpper, bool tightLower){

    if(idx == Y.size()){
        return {1, 0};
    }
    if(visited[idx][tightUpper][tightLower]){
        return memo[idx][tightUpper][tightLower];
    }

    int upperLimit = tightUpper ? (Y[idx] - '0') : 9;
    int lowerLimit = tightLower ? (X[idx] - '0') : 0; 
    long long soma = 0, quantSufix = 0;

    // for(int i=lowerLimit;i<=upperLimit;i++){
    //     soma += i;
    // }
    for(int i = lowerLimit; i<=upperLimit;i++){

        bool newTightUpper = tightUpper && (i == Y[idx] - '0');
        bool newToghtLower = tightLower && (i == X[idx] - '0');
        // bool newStarted = started || (!i); 
        
        soma = soma + (solve(idx+1, newTightUpper, newToghtLower).first * i) + (solve(idx+1, newTightUpper, newToghtLower).second);
        quantSufix = quantSufix + solve(idx+1, newTightUpper, newToghtLower).first;
    }
    visited[idx][tightUpper][tightLower] = true;
    return memo[idx][tightUpper][tightLower] = {quantSufix, soma};
}

int main(){

    int t;
    cin >> t;
    while(t--){
        string x, y;
        cin >> x >> y;
        while(x.size() < y.size()) x = '0' + x;
        X = x; Y = y;
        memset(visited, 0, sizeof(visited));
        long long resp = solve(0, true, true).second;
        
        cout << resp << endl;
    }

    return 0;
}