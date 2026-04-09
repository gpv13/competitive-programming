#include<bits/stdc++.h>
using namespace std;

long int gcd(long int a, long int b){
    while(b > 0){
        a = a % b;
        a ^= b; b ^= a; a ^= b;
    }
    return a;
}

int main(){

    long long int mdcprim;
    long long int y, passos;
    cin >> y >> passos;

    vector<int> fact;

    for(long long i=2;i*i<=y;i++){

        // if(y%i == 0){
        //     fact.push_back(i);
        // }
        while(y%i == 0) {y/=i; fact.push_back(i);}

    }
    if(y!=1) fact.push_back(y);
    // for(auto l : fact) cout << l << " ";
    long long mult = 1, resp = 1;

    for(int i=0;i<fact.size();i++){

        long long int aux = mult;
        mult *= fact[i];
        long long int auxpass = passos;
        passos -= min(passos, (mult - resp)/resp);
        if(passos == 0){
            resp+= auxpass*aux;
            break;
        }
        resp+= aux*((mult - resp)/resp);
    }

    if(passos){
        resp+=mult*passos;
    }
    cout << resp << endl;

    return 0;
}