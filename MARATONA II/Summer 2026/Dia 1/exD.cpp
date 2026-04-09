#include<bits/stdc++.h>
using namespace std;

#define MAXN 40000

int bit[MAXN];

void add( int pos, int inc ) {
	pos++;
	while ( pos < MAXN ) {
		bit[pos] += inc;
		pos += pos & -pos;
	}
}

int sum( int pos ) {
	int ret = 0;
	pos++;
	while ( pos > 0 ) {
		ret += bit[pos];
		pos -= pos & -pos;
	}
	return ret;
}



int main(){
    map<int,int> lastOcurr;
    int n, q;
    cin >> n;
    vector<int>nums(n);
    for(int i=0;i<n;i++){
        cin >> nums[i];
    }
    cin >> q;
    vector<pair<pair<int,int>,int>>queries(q); //r , l, ind
    for(int i=0;i<q;i++){
        int l, r;
        cin >> l >> r;
        l--; r--;
        queries[i] = {{r,l}, i};
    }
    sort(queries.begin(), queries.end());
    int pos = 0;
    vector<int> ans(q);
    for(int i=0;i<queries.size();i++){
        for(int j=pos;j<=queries[i].first.first;j++){

            if(lastOcurr.count(nums[j])){
                add(lastOcurr[nums[j]], -1);
                add(j, 1);
                lastOcurr[nums[j]] = j;
            }else{
                add(j, 1);
                lastOcurr[nums[j]] = j;
            }

            pos++;
        }
        // for(int i=0;i<5;i++) cout << sum(i) << " ";
        // cout << endl;
        ans[queries[i].second] = sum(queries[i].first.first) - sum(queries[i].first.second - 1);
    }
    for(int i=0;i<q;i++){
        cout << ans[i] << endl;
    }
    cout << endl;


    return 0;
}