//correct
#include <bits/stdc++.h>
using namespace std;

int main(){

    int n, result = 0;
    cin >> n;
    string word;
    cin >> word;
    for(int i =0; i<n; i++){
        if((word[i] == 'a' && word[i+1] == 'a') || (word[i] == 'a' && word[i-1] == 'a')){
            result++;
        }
    }
    cout << result << endl;


    return 0;
}
