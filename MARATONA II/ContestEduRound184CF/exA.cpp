#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n, a;
        cin >> n >> a;
        int countMenor = 0, countMaior = 0;
        bool achou = false;
        for(int i=0;i<n;i++){
            int aux;
            cin >> aux;
            if(!achou && aux >= a){
                if(aux == a) {countMenor = i; countMaior = n - i - 1;}
                else {countMenor =i+1; countMaior = n - i}
            }
        }
        if(countMenor>countMaior) cout << a-1 << endl;
        else cout << a+1 << endl;
    }



    return 0;
}