#include <bits/stdc++.h>
using namespace std;

int main() {
    int n, a, b;
    cin >> n >> a >> b;
    double k = b-a+1;
    vector<double> v(n+a+1, 0);
    if(a == 0){
        v[1] = k/(k-1);
        for(int i = 2; i <= n; i++){
            v[i] = (k*v[i-1]-v[max(0, i-b-1)])/(k-1);
        }
    }
    else{
        for(int i = 1; i <= a; i++)
            v[i] = 1;
        for(int i = a+1; i <= n; i++){
            v[i] = v[i-1] - v[max(0,i-b-1)]/k + v[i-a]/k;
        }
    }
    cout << fixed << setprecision(10) << v[n] << endl;

    return 0;
}