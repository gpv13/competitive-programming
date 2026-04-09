#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    vector<vector<int>> m(11, vector<int>(11, 0));
    int inv = 0;
    for(int j = 0; j < n; j++)
    {
        int d, l, r, c;
        cin >> d >> l >> r >> c;
        if(inv)
            continue;
        
        if(d){
            for(int i = r; i < r+l; i++){
                if(i > 10){
                    inv = 1;
                    break;
                }
                if(m[i][c]){
                    inv = 1;
                    break;
                }
                m[i][c] = 1;
            }
        }
        else{
            for(int i = c; i < c+l; i++){
                if(i > 10){
                    inv = 1;
                    break;
                }
                if(m[r][i]){
                    inv = 1;
                    break;
                }
                m[r][i] = 1;
            }
        }
    }
    if(inv)
        cout << "N" << endl;
    else
        cout << "Y" << endl;
    return 0;
}