#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    vector<int> feiticosCima(n), feiticosBaixo(n);
    for(int i=0;i<n;i++){

        cin >> feiticosCima[i]; 

    }
    for(int i=0;i<n;i++){

        cin >> feiticosBaixo[i]; 

    }
    int m;
    cin >> m;
    vector<int> fraquezasCima(m), fraquezasBaixo(m);
    for(int i=0;i<m;i++){
        cin >> fraquezasCima[i];
    }
    for(int i=0;i<m;i++){
        cin >> fraquezasBaixo[i];
    }

    vector<pair<int, int>> pre(n);
    pre[0].first = feiticosCima[0]; pre[0].second = feiticosBaixo[0];
    for(int i=1;i<n;i++){

        pre[i].first = max(feiticosCima[i], pre[i-1].first);
        pre[i].second = max(feiticosBaixo[i], pre[i-1].second);

    }
    for(auto n : pre){
        cout << n.first << " ";
    }
    cout << endl;
    for(auto n : pre){
        cout << n.second << " ";
    }
    lower_bound(pre.begin(), pre.end(), 3);
    
    return 0;
}