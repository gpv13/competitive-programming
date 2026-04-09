#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    
    for(int i=0;i<n;i++){

        int k, a, b, x, y;
        cin >> k >> a >> b >> x >> y;

        int menor = min(x, y);
        int maior = max(x, y);
        int quant = 0;

        int menortemp, maiortemp;
        if(x<y){
            menortemp = a;
            maiortemp = b;
        }else{
            menortemp = b;
            maiortemp = a;
        }

        if(k>=menortemp){
            int quantum = (k - menortemp) / menor;
            quant += quantum;

            k-= quantum * menor;
            if(k>=menortemp){
                quant++;
                k-=menor;
            }
        }
        if(k>=maiortemp){
            int quantdois = (k - maiortemp)/maior;
            quant+= quantdois;
            if(k>=maiortemp){
                quant++;
                k-=maior;
            }
        }
        cout << quant << endl;
        
    }


    return 0;
}