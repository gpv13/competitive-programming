#include<bits/stdc++.h>
using namespace std;

int main(){

    int c;
    cin >> c;
    vector<int> nums(c);
    for(int i=0;i<c;i++){
        cin >> nums[i];
    }

    int best = 0;
    int aux = 0;

    for(int i=0;i<c;i++){
        aux+=nums[i];
        best = max(best, aux);
    }

    cout << 100 + best << endl;

    return 0;
}