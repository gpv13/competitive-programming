#include <bits/stdc++.h>
using namespace std;

int main() {
    
    int n, k;
    cin >> n >> k;
    string s, result;
    cin >> s;
    result = s;
    int ocount = 0, qcount = 0;
    for(int i =0; i<n;i++){

        if(s[i] == 'o'){
            ocount++;
        }
        if(s[i] == '?'){
            if(s[i-1] == 'o' || s[i+1] == 'o'){
                result[i] = '.';
            }else{
                result[i] = '?';
                qcount++;
            }
        }
    }
    if(ocount==k){
        for(int i=0;i<n;i++){
            if(result[i] == '?') result[i] = '.';
        }
    }
    if((qcount == k - ocount) && ocount != k){
        for(int i =0; i<n; i++){
            if(result[i] == '?' && result[i-1] != 'o' && result[i+1] != 'o'){
                ocount++; 
                result[i] = 'o';
            }else if(result[i] == '?'){
                result[i] = '.';
            }
        }
    }
    if(ocount==k){
        for(int i=0;i<n;i++){
            if(result[i] == '?') result[i] = '.';
        }
    }
    cout << result << endl;
    return 0;
}
