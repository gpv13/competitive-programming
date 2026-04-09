#include<bits/stdc++.h>
using namespace std;

vector<int> sliding_window_max(const vector<int>& arr, int k) {
    int n = arr.size();
    vector<int> result;
    deque<pair<int, int>> dq;

    for (int i = 0; i < n; ++i) {
        if (!dq.empty() && dq.front().second <= i - k) {
            dq.pop_front();
        }

        while (!dq.empty() && dq.back().first <= arr[i]) {
            dq.pop_back();
        }

        dq.push_back({arr[i], i});

        if (i >= k - 1) {
            result.push_back(dq.front().first);
        }
    }
    return result;
}

vector<int> sliding_window_max_col(const vector<vector<int>>& arr, int k, int pos) {
    int n = arr.size();
    vector<int> result;
    deque<pair<int, int>> dq;

    for (int i = 0; i < n; ++i) {
        if (!dq.empty() && dq.front().second <= i - k) {
            dq.pop_front();
        }

        while (!dq.empty() && dq.back().first <= arr[i][pos]) {
            dq.pop_back();
        }

        dq.push_back({arr[i][pos], i});

        if (i >= k - 1) {
            result.push_back(dq.front().first);
        }
    }
    return result;
}


int main(){

    int n, m, k, q;
    cin >> n >> m >> k >> q;
    vector<vector<int>> mat(n, vector<int>(m, -1));
    for(int i=0;i<q;i++){
        int x, y, v;
        cin >> x >> y >> v;
        mat[y-1][x-1] = v;
    }
    vector<vector<int>> lines_max(n);
    for(int i=0;i<n;i++){
        
        vector<int> aux = sliding_window_max(mat[i], k);
        lines_max[i] = aux;
    }
    vector<vector<int>> sub_max(m-k+1);
    for(int i=0;i<m-k+1;i++){
        
        vector<int> aux = sliding_window_max_col(lines_max, k, i);
        sub_max[i] = aux;
    }
    int menor = INT32_MAX;
    for(int i=0;i<sub_max.size();i++){
        for(int j=0;j<sub_max[i].size();j++){
            menor = min(menor, sub_max[i][j]);
        }
    }
    cout << menor << endl;
    return 0;
}