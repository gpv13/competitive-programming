#include<bits/stdc++.h>
using namespace std;

int main(){


    vector<vector<int>>matriz(51, vector<int>(51));
    int n;
    cin >> n;
    for(int i=0;i<n;i++){
        for(int j=0;j<n;j++){
            cin >> matriz[i][j];
        }
    }
    if(matriz[0][0] < matriz[0][1] && matriz[0][0] < matriz[1][0]){
        cout << "0" << endl;
    }else if(matriz[0][0] > matriz[0][1] && matriz[0][0] > matriz[1][0]){
        cout << "2" << endl;
    }else if(matriz[0][0] > matriz[0][1] && matriz[0][0] < matriz[1][0]){
        cout << "1" << endl;
    }else if(matriz[0][0] < matriz[0][1] && matriz[0][0] > matriz[1][0]){
        cout << "3" << endl;
    }

    return 0;
}