#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    int count = 0;
    vector<pair<tuple<int, int, int>, int>> cartas;
    vector<pair<int, int>> possiveis;
    for(int i=1;i<=n;i++){

        int a, b, c;
        cin >> a >> b >> c;
        tuple<int,int,int> carta = {a, b, c};
        cartas.push_back({carta, i});
        count++;

    }
    bool Mudou = true;
    sort(cartas.begin(), cartas.end());

        for(int i=1;i<n;i++){
            auto [um, dois, tres]  = cartas[i].first;
            auto [prim, sec, third] = cartas[i-1].first;
            if(cartas[i].second && cartas[i-1].second && um == prim){
                
                possiveis.push_back({cartas[i].second, cartas[i-1].second});
                cartas[i].second = 0;
                cartas[i-1].second = 0;
                
            }
        }

    set<int> banana;
        

    cout << count << endl;
    for(int i=1;i<=n;i++){
        cout << i << " " << i << endl;
    }


    return 0;
}