#include<bits/stdc++.h>
using namespace std;

int query(int L, int R, long long lg2[], long long[] st) {
    int j = lg2[R - L + 1]; // Pré-calcule os logaritmos para ser O(1)
    return __gcd(st[L][j], st[R - (1 << j) + 1][j]);
}

int main(){

    int n;
    cin >> n;
    vector<int>nums(n);
    for(int i=0;i<n;i++){
        cin >> nums[i];
    }

    long lg2[n+1];
    lg2[1] = 0;
    for (int i = 2; i <= n; i++)lg2[i] = lg2[i/2] + 1;

    long long st[21][n];

    copy(nums.begin(), nums.end(), st[0]);
    for(int i=1;i<21;i++){
        for(int j=0;j + (1 << i) <= n;j++){
            st[i][j] = __gcd(st[i-1][j],st[i-1][j + (1 << (i-1))]);
        }
    }

    map<int,int> ans;

    for(int i=0;i<n;i++){
        int k = i;
        while(k<n){



        }
    }


    int q;
    cin >> q;
    for(int i=0;i<q;i++){
        int x;
        cin >> x;
    }


    return 0;
}