#include <bits/stdc++.h>
using namespace std;

int main(){

    float x1, x2, x3, y1, y2, y3, xV, yV;

    cin >> x1 >> y1;
    cin >> x2 >> y2;
    cin >> x3 >> y3;
    cin >> xV >> yV;

    if(max({x1, x2, x3}) >= xV && max({y1, y2, y3}) >= yV && min({x1, x2, x3}) <= xV && min({y1, y2, y3})<= yV){
        cout << "Dentro" << endl;
    }else{
        cout << "Fora" << endl;
    }



    return 0;
}