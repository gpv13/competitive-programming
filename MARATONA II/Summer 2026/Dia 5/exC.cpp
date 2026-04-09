#include<bits/stdc++.h>
using namespace std;
int main(){

    int n;
    cin >> n;
    bool temDiag = false;
    vector<vector<int>> mex(101, vector<int>(101, -1));
    vector<pair<int,int>> coords;
    for(int i=0;i<n;i++){
        int l, c;
        cin >> l >> c;
        if(l==c) temDiag = true;
        coords.push_back({l,c});
    }
    for(int i=0;i<101;i++){
        mex[0][i] = INT32_MAX;
        mex[i][0] = INT32_MAX;
        mex[i][i] = INT32_MAX;
    }
    for(int i=0;i<101;i++){
        for(int j=0;j<101;j++){

            if(mex[i][j] == -1){
                set<int>aux;
                for(int k=i-1;k>=0;k--){
                    aux.insert(mex[k][j]);
                }
                for(int k=j-1;k>=0;k--){
                    aux.insert(mex[i][k]);
                }
                
                pair<int,int> cor = {i-1, j-1};

                while(cor.first >=0 && cor.second >= 0){
                    aux.insert(mex[cor.first][cor.second]);
                    cor.first--; cor.second--;
                }
                int numero = 0;
                while(aux.count(numero)) numero++;
                mex[i][j] = numero;

            }

        }
    }
    int xr = 0;
    for(int i=0;i<coords.size();i++) xr ^= mex[coords[i].first][coords[i].second];

    if(temDiag) cout << "Y" << endl;
    // else if(n==1){
    //     if((coords[0].first == 1 && coords[0].second == 2) || (coords[0].first == 2 && coords[0].second == 1)){
    //         cout << "N" << endl;
    //     }else{
    //         cout << "Y" << endl;
    //     }
    else if(xr){
        cout << "Y" << endl;
    }else{
        cout << "N" << endl;
    }
 

    return 0;
}