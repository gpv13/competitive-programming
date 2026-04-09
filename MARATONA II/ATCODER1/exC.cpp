#include<bits/stdc++.h>
using namespace std;

int main(){
    map<pair<int, int>, int> matriz;
    int n, m, q;
    cin >> n >> m >> q;
    for(int i =0;i<q;i++){
        int tipo, x, y;
        cin >> tipo;
        if(tipo == 1){
            cin >> x >> y;
            matriz[make_pair(x, y)] = 1;
        }
        if(tipo == 2){
            cin >> x;

            matriz[make_pair(x, 0)] = 1;

        }
        if(tipo == 3){
            cin >> x >> y;
            if(matriz[{x, y}] == 1 || matriz[{x, 0}] == 1){
                cout << "Yes" << endl;
            }else{
                cout << "No" << endl;
            }
        }
    }

    return 0;
}