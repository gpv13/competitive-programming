#include<bits/stdc++.h>
using namespace std;

int main(){

    int max = 1000002;
    vector<double> numeros(max); vector<int>expo(max);
    numeros[0] = 1.0;
    numeros[1] = 1.0;
    expo[0] = 0;
    expo[1] = 0;
    for(int i=2;i<max;i++){

        float aux = numeros[i - 1] * i;
        bool maior = false;
        if(aux >= 10.0){
            int conta = 0;
            while(aux>=10.0){
                aux/=10.0;
                conta++;
            }
            numeros[i] = aux;
            expo[i] = expo[i-1] + conta;
        }else{
            numeros[i] = aux;
            expo[i] = expo[i-1];
        }
    }
    int n;
    cin >> n;
    cout << fixed << setprecision(2); 
    for(int i=0;i<n;i++){
        int num;
        cin >> num;
        cout << numeros[num] << "*10^" << expo[num] << endl;
    }

}