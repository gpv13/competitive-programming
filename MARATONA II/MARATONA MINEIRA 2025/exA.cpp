#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    set<pair<pair<int,int> , pair<int, int>>> posicoes; //dist, desempate, posicaoinicio, posicaofim
    vector<int> listaFim(n);
    listaFim[0] = 1;
    if(n>1)listaFim[n-1] = 2;
    posicoes.insert({{n, n-1} ,{0, n-1}});
    //cout << "1";
    for(int i = 3; i<=n;i++){
        auto it = --posicoes.end();
        pair<pair<int,int>, pair<int,int>> primeiro = *it;
        //cout << primeiro.second;
        listaFim[primeiro.second.second - primeiro.first.first/2] = i;
        //cout << primeiro.first.first << " " << primeiro.first.second << " " << primeiro.second.first << " " << primeiro.second.second << endl; 
        //cout << "ue";
        posicoes.erase(it);
        //cout << "ue";
        pair<pair<int,int>, pair<int,int>> novo1, novo2;
        novo1 = {{(primeiro.second.second - primeiro.first.first/2) - primeiro.second.first + 1 , (n-1) - primeiro.second.first}, {primeiro.second.first, primeiro.second.second - primeiro.first.first/2}};
        novo2 = {{(primeiro.second.second - (primeiro.second.second - primeiro.first.first/2)) + 1 , (n-1) - (primeiro.second.second - primeiro.first.first/2)}, {primeiro.second.second - primeiro.first.first/2 , primeiro.second.second }};
        if(novo1.first.first!=0)posicoes.insert(novo1);
        if(novo2.first.first!=0)posicoes.insert(novo2);
        //cout << i;
    }
    //cout << "dps";
    bool primeiro = true;
    for(int i=0;i<n;i++){
        if(primeiro) cout << listaFim[i];
        else cout << " " << listaFim[i];
        primeiro = false;
    }
    cout << endl;

    return 0;
}