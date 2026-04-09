#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    for(int i=1;i<=t;i++){

        int n;
        cin >> n;
        int num;
        vector<int> lista, diferencas;
        long long int menor = 100000000000;
                int maiorescada;
        for(int j=0;j<n;j++){
            cin >> num;
            lista.push_back(num);
            if(j>0) diferencas.push_back(abs(num - lista[j-1]));
            if(num > maiorescada) maiorescada = num;
        }


        
        for(int j=0;j<n-1;j++){

            if(max(lista[j+1] , abs(lista[j] - lista[j+1])) < maiorescada) maiorescada = max(lista[j+1] , abs(lista[j] - lista[j+1])); 

        }
        for(int j=n-1;j>0;j--){

            if(max(lista[j-1] , abs(lista[j] - lista[j-1])) < maiorescada) maiorescada = max(lista[j-1] , abs(lista[j] - lista[j-1])); 

        }
        //if(menor > maiorescada) maiorescada = menor;
        
        cout << "Case #" << i << ": " << maiorescada << endl;

    }


    return 0;
}