#include<bits/stdc++.h>
using namespace std;

int n;
vector<double> sushis(300);
double memo[300]; //id
bool visited[300];
double solve(int id, int ){

}

int main(){

    cin >> n;
    memset(visited, false, sizeof(visited));
    for(int i=0;i<n;i++){
        cin >> sushis[i];
    }
    cout << fixed << setprecision(12);
    cout << solve(0,0,0) << endl;


    return 0;
}