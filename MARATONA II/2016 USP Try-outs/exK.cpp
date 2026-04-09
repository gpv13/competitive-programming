#include<bits/stdc++.h>
using namespace std;

int main(){

    int dias;
    cin >> dias;
    float prob = 1.0;
    int pessoas = 1;
    while(prob>=0.5){

        pessoas++;
        prob = prob * (double)(dias - (pessoas - 1)) / dias;

    } 
    cout << pessoas << endl;

    return 0;
}