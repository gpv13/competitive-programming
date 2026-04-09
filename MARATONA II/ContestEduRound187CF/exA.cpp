#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >>t;
    while(t--){
        int n, m, d;
        cin >> n >> m >> d;
        int quantaPilha = 1 + (d/m);
        cout << ceil((double)((double)n/(double)quantaPilha)) << endl;
    }

    return 0;
}