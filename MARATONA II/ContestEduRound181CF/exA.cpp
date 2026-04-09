#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;

    for(int j=0;j<t;j++){

        string s;
        cin >> s;

        string t, sufix;
        for(char c: s){
            if(c == 'T') t += 'T';
            else sufix += c;
        }
        string result = t;
        result += sufix;
        cout << result << endl;
    }



    return 0;
}