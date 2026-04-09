#include<bits/stdc++.h>
using namespace std;

long long int gcd(long long int a, long long int b) {
    
    while (b != 0) {
        long long int temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}



int main(){

    int t;
    cin >> t;
    for(int j=0;j<t;j++){

        long long int x, y, k, result;
        cin >> x >> y >> k;
        long long int div = gcd(x, y);
        if(x/div <= k && y/div <= k){
            result = 1;
            cout << result << endl;
        }else{ 
            result = 2;
            cout << result << endl;
        }
    }

    return 0;
}