#include <bits/stdc++.h>
using namespace std;

void solve() {
    long long n;
    cin >> n;
    vector<int> nums(n);
    for(int i=0;i<n;i++)cin >> nums[i];
    


    long long cont = 0;

    vector<bool> visited(n,false);

    for(int i=0;i<n;i++){
        if(visited[i]) continue;
        for(int j=i+nums[i];j<n;j+=nums[i]){
            if(j-i == nums[i] * nums[j]) {cont++; cout << "(" << i << ", " << j << ")" << endl;}
            if(nums[j] == nums[i]) visited[j] = true;
        }
    }


    cout << cont << endl;

}

int main() {
    int t;
    cin >> t;
    while (t--) {
        solve();
    }
    return 0;
}