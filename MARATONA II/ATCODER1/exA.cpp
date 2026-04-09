#include<bits/stdc++.h>
using namespace std;

int main(){

    int n, soma =0;;
    cin >> n;
    for(int i=1;i<=n;i++){
        int aux;
        cin >> aux;
        if(i%2 !=0) soma+=aux;
    }
    cout << soma << endl;
    
    return 0;
}