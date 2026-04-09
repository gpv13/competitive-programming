#include<bits/stdc++.h>
using namespace std;

long long int soma = 0;

void solve(int n, int p){

    if(p %2 != 0){
        soma += (p+1)/2;
        return;
    }else{
        soma += p/2;
        solve((n-p) + p/2, (n-p) + p/2);
    }


}

int main(){

    int t;
    cin >> t;

    for(int i=0;i<t;i++){
        soma = 0;
        int n, p;
        cin >> n >> p;
        solve(n, p);

        cout << soma << endl;
    }



    return 0;
}