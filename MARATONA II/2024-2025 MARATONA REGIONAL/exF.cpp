#include<bits/stdc++.h>
using namespace std;

int main(){

    vector<int>nums (41);
    nums[1] = 1;
    nums[2] = 2;
    for(int i=3;i<41;i++){
        nums[i] = nums[i-1] + nums[i-2];
    }
    int n;
    cin >> n;
    cout << nums[n] << endl;


    return 0;
}