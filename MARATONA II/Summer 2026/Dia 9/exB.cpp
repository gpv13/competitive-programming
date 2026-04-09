#include<bits/stdc++.h>
using namespace std;
int main(){

    long long int n;
    cin >> n;
    vector<long long int>bacs (n);
    priority_queue<long long int, vector<long long int>, greater<long long int>> pq;
    for(long long int i=0;i<n;i++){
        cin >> bacs[i];
    }
    pq.push(__builtin_ctz(bacs[0]));
    bool ok = true;
    for(long long int i=1;i<n;i++){
        long long int x = (bacs[i-1] >> __builtin_ctz(bacs[i-1]));
        if((bacs[i] >> __builtin_ctz(bacs[i])) != x) ok = false;
        pq.push(__builtin_ctz(bacs[i]));
    }
    if(!ok){
        cout << "-1" << endl;
        return 0;
    }
    long long int ans = 0;
    while(pq.size() > 1){
        long long int x = pq.top(); pq.pop();
        long long int y = pq.top(); pq.pop();

        ans += (y-x);
        pq.push(y+1);
    }

    cout << ans << endl;

    return 0;
}