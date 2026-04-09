#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;

    for(int i=0;i<n;i++){

        int t, s;
        cin >> t >> s;
        int menor, maior;
        for(int j=0;j<t;j++){
            int aux;
            cin >> aux;
            if(j==0) menor = aux;
            if(j==t-1) maior = aux;
        }
        int prim = min(abs(s-menor), abs(maior-s));
        int total = prim + ( maior - menor);
        cout << total << endl;
    }



    return 0;
}