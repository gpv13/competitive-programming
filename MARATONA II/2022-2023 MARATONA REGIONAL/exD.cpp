#include<bits/stdc++.h>
using namespace std;
int main(){

    int n, x, y;
    cin >> n >> x >> y;
    int conta = 0;
    int posy = (1<<n)/2, posx = (1<<n)/2;
    pair<int,int> posIni = {posx, posy};
    pair<int,int> pontoEsqBaixo = {0,0}, pontoEsqCima = {0, 1 << n}, pontoDirCima = {1 << n, 1 << n}, pontoDirBaixo = {1 << n, 0};
    while(posy != y && posx != x){

        if(posy > y && posx > x){
            y = (y*2); x = (x*2);
        }else if(posy > y && posx < x){
            y = (y*2); x = (x*2) - (1<<n);
        }else if(posy < y && posx > x){
            y = (y*2)-(1<<n); x=(x*2);
        }else{
            y = (y*2)-(1<<n); x = (x*2) - (1<<n);
        }

        conta++;
    }

    cout << conta << endl;

    return 0;
}