#include<bits/stdc++.h>
using namespace std;
#define INF 100000000
int main(){

    vector<int> custos;
    vector<int> best;
    int n;

    cin >> n;
    custos.resize(n+1);
    best.resize(n+1);
    for(int i = 1; i<=n; i++){
        cin >> custos[i];
    }
    custos[0] = INF;
    best[0] = 0; 
    best[1] = 0;
    for(int i=2;i<=n;i++){
        best[i] = min(best[i-1] + abs(custos[i] - custos[i-1]), best[i-2] + abs(custos[i] - custos[i-2]));
    }
    cout << best[n] << endl;

    return 0;
}