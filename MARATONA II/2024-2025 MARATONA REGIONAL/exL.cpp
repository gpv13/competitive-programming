#include<bits/stdc++.h>
using namespace std;

int main(){

    vector<int>bits(40, 0);

    int n;
    cin >> n;
    for(int i=0;i<n;i++){
        int aux;
        cin >> aux;
        int import = 0;
        while(aux>0){
            
            if(aux%2 == 1){
                bits[import]++;
            }
            aux/=2;
            import++;
        }
    }
    bool primeiro = true;
    for(int i=0;i<n;i++){
        int num = 0;
        for(int j=0;j<40;j++){
            if(bits[j]){

                num += pow(2, j);
                bits[j]--;
            }
        }
        if(primeiro) cout << num;
        else cout << " " << num;

        primeiro = false;
    }
    cout << endl;

    return 0;
}