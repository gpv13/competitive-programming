#include<bits/stdc++.h>
using namespace std;
//CORRETO!

int main(){

    int n;
    cin >> n;
    vector<long long int> lista;
    for(int i=0;i<n;i++){

        long long int aux;
        cin >> aux;
        lista.push_back(aux);

    }
    sort(lista.begin(), lista.end());
    int indice;
    long long int valor, total = 0;
    for(int i=0;i<n;i++){

        if(lista[i] * (n - i) > total){
            total = lista[i] * (n - i);
            valor = lista[i];
        }

    }
    cout << valor << " " << total << endl;

    return 0;
}