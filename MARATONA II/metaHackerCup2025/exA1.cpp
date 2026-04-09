#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    for(int i=1;i<=t;i++){

        int n;
        cin >> n;
        int num;
        int prox = -1;
        int maiordist = 0;
        for(int j=0;j<n;j++){
            cin >> num;
            if(prox!=-1){
                if(abs(prox - num) > maiordist) maiordist = abs(prox-num);
            }
            prox = num;
        }
        if(prox!=-1){
            if(abs(prox - num) > maiordist) maiordist = abs(prox-num);
        }
        cout << "Case #" << i << ": " << maiordist << endl;

    }


    return 0;
}