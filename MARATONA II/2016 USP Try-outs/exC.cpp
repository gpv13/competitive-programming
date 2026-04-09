#include<bits/stdc++.h>
using namespace std;

int main(){

    int h, w;
    cin >> h >> w;
    vector<int> paredeEsq(h);
    for(int i=0;i<h;i++){
        cin >> paredeEsq[i];
    }
    int menorDist;
    for(int i=0;i<h;i++){
        int aux;
        cin >> aux;
        if(i == 0) menorDist = w - (paredeEsq[i] + aux);
        else if(menorDist > w - (paredeEsq[i] + aux)) menorDist = w - (paredeEsq[i] + aux);
    }
    float result = (float)menorDist / 2;

    cout << result << endl;

    return 0;
}