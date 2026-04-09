#include<bits/stdc++.h>
using namespace std;

int main(){

    long long n;
    cin >> n;
    long long aux = 0;
    long long conta = 0;
    set<long long> poss;
    for(long long i = 2; i<=n+1;i*=2){
        poss.insert(i);
        poss.insert(i+1);
        aux = i;
        conta++;
    }
    if(poss.count(n)){
        if(n%2){
            cout << "A";
            for(int i=0;i<log2(n)-1;i++){
                cout << "AB";   
            }
            cout << endl;
        }else{
            for(int i=0;i<log2(n);i++){
                cout << "AB";
            }
            cout << endl;
        }
    }else{
        cout << "IMPOSSIBLE" << endl;
    }

    return 0;
}