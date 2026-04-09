#include<bits/stdc++.h>
using namespace std;

int main(){


    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        set<int> lista;
        for(int i=0;i<n;i++){

            int aux;
            cin >> aux;

            lista.insert(aux);

        }
        int tam = lista.size();
        cout << *(lista.lower_bound(tam)) << endl;
    }


    return 0;
}