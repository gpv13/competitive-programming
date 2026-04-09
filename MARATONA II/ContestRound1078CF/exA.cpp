#include<bits/stdc++.h>
using namespace std;
int main(){

    long long int t;
    cin >> t;
    while(t--){
        long long int n,w;
        cin >> n >> w;

        cout << n - (n/w) << endl;

    }

    return 0;
}