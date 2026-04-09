#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;

    for(int i=0;i<n;i++){

        int tam;
        cin >> tam;

        bool certo = false;
        string palavra;
        cin >> palavra;
        set<char>letras;
        char prim = palavra[0];
        char fim = palavra[tam-1];
        for(int j=1;j<tam-1;j++){
            
            if(letras.count(palavra[j]) || palavra[j] == prim || palavra[j] == fim) certo = true;

            letras.insert(palavra[j]);

        }

        if(certo) cout << "Yes" << endl;
        else cout << "No" << endl;
    }



    return 0;
}