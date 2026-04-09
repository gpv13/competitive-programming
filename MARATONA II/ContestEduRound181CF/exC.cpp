#include<bits/stdc++.h>
using namespace std;

long long int ans(long long int num){

    long long int ansr = num;
    ansr -= num/2;
    ansr -= num/3 - num/6;
    ansr -= num/5 - num/10 - num/15 + num/30;
    ansr -= num/7 - num/14 - num/21 - num/35 + num/42 + num/70 + num/105 - num/210; 

    return ansr;
}


int main(){

    int t;
    cin >> t;
    while(t--){

        long long int l, r;
        cin >> l >> r;
        long long int result = ans(r) - ans(l-1);
        cout << result << endl;

    }
    return 0;

}