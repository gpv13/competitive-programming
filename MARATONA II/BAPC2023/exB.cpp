#include<bits/stdc++.h>
using namespace std;

int main(){


    long long int n;
    cin >> n;

    long double nf = (long double)n;
    long long int count = 0;
    while(nf>1){

        nf = nf/2;
        count++;

    }
    count++;
    cout << count << endl;


    return 0;
}