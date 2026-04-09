#include<bits/stdc++.h>
using namespace std;

int main(){

    vector<int> cartas(14, 0);

    int n;
    cin >> n;
    int totalcomum = 0;
    int m1, m2, j1, j2;
    cin >> j1 >> j2;
    cin >> m1 >> m2;
    cartas[m1]++; cartas[m2]++; cartas[j1]++; cartas[j2]++;

    if(j1>10)j1=10; if(j2>10)j2=10; if(m1>10)m1=10; if(m2>10)m2=10;

    int totalmaria = m1 + m2, totaljoao = j1 + j2;
    for(int i = 0; i<n;i++){
        int aux;
        cin >> aux;
        cartas[aux]++;
        if(aux>10)aux=10;
        totalcomum+=aux;
    }
    totaljoao += totalcomum;
    totalmaria += totalcomum;
    
    int cartaescolhida;

    if(totaljoao > totalmaria){
        cartaescolhida = 24 - totaljoao;
        while(cartas[cartaescolhida] == 4){
            cartaescolhida++;
        }
        int pontoscarta = cartaescolhida;
        if(pontoscarta > 10) pontoscarta = 10;
        if(totalmaria + pontoscarta > 23) cartaescolhida = -1;
    }else{
        cartaescolhida = 23 - totalmaria;
        while(cartas[cartaescolhida] == 4){
            cartaescolhida++;
        }
        int pontoscarta = cartaescolhida;
        if(pontoscarta > 10) pontoscarta = 10;
        if(totalmaria + pontoscarta > 23) cartaescolhida = -1;
    }
    cout << cartaescolhida << endl;


    return 0;
}