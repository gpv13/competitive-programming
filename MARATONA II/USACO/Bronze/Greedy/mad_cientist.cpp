#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    string a, b;
    cin >> a;
    cin >> b;
    int conta = 0;
    bool certo = true;
    for(int i=0;i<n;i++){
        if(certo && a[i]!=b[i]){
            certo = false;
            conta++;
        }
        if(a[i] == b[i]){
            certo = true;
        }
    }
    cout << conta << endl;

    return 0;
}