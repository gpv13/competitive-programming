#include<bits/stdc++.h>

using namespace std;

int main(){

    int t, n;
    int tempo = 0;
    int intervalo;
    cin >> n;
    cin >> t;

    bool certo = false;
    intervalo = n -1; 
    while(!certo){


        if((n* (tempo + 1)) + intervalo > t) break;
        tempo++;
    }   
    cout << tempo << endl;


    return 0;
}