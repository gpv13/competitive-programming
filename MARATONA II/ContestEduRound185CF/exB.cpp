#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        int maior = 0, menor = 554321;
        vector<int>itens;
        for(int i=0;i<n;i++){
            int aux;
            cin >> aux;
            itens.push_back(aux);
            if(aux > maior) maior = aux;
            if(aux!=0 && menor > aux) menor = aux;
        }
        sort(itens.begin(), itens.end());
        
        int dist = 0;
        for(int i=0;i<itens.size();i++){
            if(itens[i] != 0)dist++;
            if(itens[i] == maior) break;
        }
        cout << dist - (n - maior) << endl;
    }
    return 0;
}