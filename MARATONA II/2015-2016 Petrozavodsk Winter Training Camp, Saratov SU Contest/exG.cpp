#include<bits/stdc++.h>
using namespace std;

struct Result{
    long long result;
    string s;

    bool operator <(const Result& r) const{
        if(result != r.result) return result < r.result;

        return false;
    }
};

//memo[idx][tightOver][tightUnder][started]
Result memo[20][2][2][2];
bool visited[20][2][2][2];
string X, Y;
Result solve_single(int idx, bool tightOver, bool tightUnder, bool started) {
    if (idx == X.size()) {
        return {1, ""};
    }
    if (visited[idx][tightOver][tightUnder][started]) 
        return memo[idx][tightOver][tightUnder][started];

    Result bestRes = {-1, ""};
    
    int limitOver = tightOver ? (Y[idx] - '0') : 9;
    int limitUnder = tightUnder ?  (X[idx] - '0') : 0;

    for (int d = limitUnder; d <= limitOver; d++) {
        bool newtightOver = tightOver && (d == limitOver);
        bool newtightUnder = tightUnder && (d == limitUnder); 
        bool newStarted = started || (d != 0);
        
        Result current = solve_single(idx + 1, newtightOver, newtightUnder, newStarted);
        if (newStarted) {
            current.result *= d;
            current.s = to_string(d) + current.s;
        }
        if(bestRes <  current){
            bestRes = current;
        }
        
        // ans *= solve_single(idx + 1, newtightOver, newtightUnder, newStarted);
    }


    visited[idx][tightOver][tightUnder][started] = true;
    return memo[idx][tightOver][tightUnder][started] = bestRes;
}

int main(){

    string x, y;
    cin >> x >> y;
    string zeros;
    int diff = y.size() - x.size();
    while(diff--){
        zeros += '0';
    }
    zeros += x;
    X = zeros; Y = y;

    Result ans = solve_single(0, true, true, false);

    cout << ans.s << endl;

    return 0;
}