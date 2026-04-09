#include<bits/stdc++.h>
using namespace std;

int main(){

    string s;
    cin >> s;
    long long conta = 0;
    for(int i=0;i<s.size();i++) if(s[i] % 4 == 0) conta++;
    for(int i=1;i<s.size();i++) if(((s[i-1] - '0')*10 + s[i]-'0') % 4 == 0) conta += i;

    cout << conta << endl;

}