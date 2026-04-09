#include<bits/stdc++.h>
using namespace std;

int main(){

    
    int n, p;
    cin >> n >> p;

    while(n || p){
        int ant = 0, prox = 0, posicao, acima;
        bool encontrado = false, proximo = false;
        for(int i=0;i<p;i++){
            int t;
            cin >> t;
            int soma = 0;
            for(int j=0;j<t;j++){
                int item;
                cin >> item;
                if(item == 1){
                    encontrado = true;
                    posicao = j;
                    acima = (t-1) - posicao; 
                }
                
                soma++;
            }
            if(!prox && proximo) prox = soma;
            if(!encontrado) ant = soma;
            if(encontrado) proximo = true;
        }
        int result;
        if(prox > posicao && ant> posicao){
            result = acima + (min(prox, ant) - posicao);
        }else{
            result = acima;
        }

        
        cout << result << endl;
        cin >> n >> p;
    }



    return 0;
}