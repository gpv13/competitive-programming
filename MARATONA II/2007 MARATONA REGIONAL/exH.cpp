#include<bits/stdc++.h>
using namespace std;
#define INF 2000000000
int main(){

    long long int t;
    cin >> t;
    while(t){
        

        int n, c, soma = 0;
        for(int i=0;i<t;i++){

            cin >> n >> c;

            soma += c - c%2;

        }
        cout << (soma - soma%4)/4 << endl;


        cin >> t;
    }  
    cout << endl;




    return 0;
}