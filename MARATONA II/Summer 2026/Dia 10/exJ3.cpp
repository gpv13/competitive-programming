#include <bits/stdc++.h>
using namespace std;

int main() {

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    
    long long n, m, l;
    if (!(cin >> n >> m >> l)) return 0;

    vector<long long> start, fini; 
    for(int i = 0; i < n; i++) {
        long long x, y;
        cin >> x >> y;
        if(y <= l) { 
            long long dist = l - y;
            start.push_back(x - dist);      
            fini.push_back(x + dist + 1);  
        }
    }

    sort(start.begin(), start.end());
    sort(fini.begin(), fini.end());
    vector<pair<long long, int>> junt;

    int posS = 0, posF = 0;
    while(posS < start.size() && posF < fini.size()){
        if(start[posS] < fini[posF]) {
            junt.push_back({start[posS], 1});
            posS++;
        }else{
            junt.push_back({fini[posF], -1});
            posF++;
        }
    }
    while(posF<fini.size()){
            junt.push_back({fini[posF], -1});
            posF++;
    }

    while(posS<start.size()){
        junt.push_back({start[posS], 1});
        posS++;
    }

    vector<pair<long long, int>> compactado;
    for(auto p : junt) {
        if(!compactado.empty() && compactado.back().first == p.first) {
            compactado.back().second += p.second;
        } else {
            compactado.push_back(p);
        }
    }    


    long long soma = 0;
    for(int i=0;i<compactado.size();i++){
        soma+=compactado[i].second;
        compactado[i].second = soma;
    }



    for(int i = 0; i < m; i++) {
        long long pos_fisher;
        cin >> pos_fisher;

        auto it = upper_bound(compactado.begin(), compactado.end(), make_pair(pos_fisher, (int)2e9));
        if(it == compactado.begin()) {
            cout << "0\n";
        } else {
            cout << prev(it)->second << "\n";
        }
    }

    return 0;
}