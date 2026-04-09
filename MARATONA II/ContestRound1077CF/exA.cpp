#include<bits/stdc++.h>
using namespace std;
int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        int menor = 1, maior = n;
        int numeros[n];
        bool menorB = true;
        for(int i=n-1;i>=0;i--){
            if(menorB){
                numeros[i] = menor;
                menor++;
                menorB = false;
            }else{
                numeros[i] = maior;
                maior--;
                menorB = true;
            }
        }
        for(int i=0;i<n;i++){
            if(!i) cout << numeros[i];
            else cout << " " << numeros[i];
        }
        cout << endl;
    }


    return 0;
}