#include<bits/stdc++.h>
using namespace std;


int bb(int l, int r){
 return (l + r)/2;
}

int main(){

    int t;
    cin >> t;
    for(int i=1;i<=t;i++){

        int n;
        cin >> n;
        int num;
        vector<int> lista;

        for(int j=0;j<n;j++){
            cin >> num;
            lista.push_back(num);
        }
        int l = 0, r = 1000000000;
        while(r>l){
            int meio = bb(l, r);
            for(int j=0;j<lista.size();j++){
                
            }
        }

        
        cout << "Case #" << i << ": " << maiorescada << endl;

    }


    return 0;
}