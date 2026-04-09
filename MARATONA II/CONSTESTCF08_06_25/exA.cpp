#include<bits/stdc++.h>
using namespace std;

int main(){

    int q;
    cin >> q;
    for(int i=0;i<q;i++){

        int n, x;
        cin >> n >> x;
        bool errado = false;
        bool porta = false;
        vector<int> portas(12);
        for(int j=1;j<=n;j++){
            
            cin >> portas[j];
        }
        for(int j=1;j<=n;j++){
            
            if(portas[j] == 1 && !porta){
                j+=x-1;
                porta=true;
            }else if(portas[j] == 1){
                errado = true;
            }
        }
            
        if(errado) cout << "NO" << endl;
        else cout << "YES" << endl;
    }

    
    return 0;
}