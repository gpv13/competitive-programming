#include<bits/stdc++.h>
using namespace std;

int main(){

    int degree;
    cin >> degree;
    string instructions;
    cin >> instructions;
    bool full = false;
    int maxD = 0, maxE = 0, curr = 0;
    int divid = ceil(360.0/(float)degree);
    for (int i = 0; i < instructions.length(); i++){
        if(instructions[i] == 'D'){
            curr++;
            maxD = max(maxD, curr);
        }
        if(instructions[i] == 'E'){
            curr--;
            maxE = min(maxE, curr);
        }
        if(abs(maxE)+maxD >=divid)full = true;
    }
    if(full) cout << "S" << endl;
    else cout << "N" << endl;

    return 0;
}