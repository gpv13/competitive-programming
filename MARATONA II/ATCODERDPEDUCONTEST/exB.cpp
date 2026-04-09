#include<bits/stdc++.h>
using namespace std;
#define INF 10000000000
int main(){

    int n, k;
    cin >> n >> k;
    vector<int> custos(n+1);
    vector<int> best(n+1, INF);

    for(int i = 1; i<=n; i++){
        cin >> custos[i];
    }

    best[1] = 0;
    for(int i=2;i<=n;i++){
        for(int j=max(1, i - k);j<i;j++){
            best[i] = min(best[i], best[j] + abs(custos[i] - custos[j]));
        }
    }
    cout << best[n] << endl;

    return 0;
}