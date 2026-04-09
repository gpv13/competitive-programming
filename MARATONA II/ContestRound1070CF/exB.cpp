#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        string word;
        cin >> word;
        int borderLeft = 0, borderRight = 0;
        int k = 0;
        while(word[k] != '1' && k<n){
            borderLeft++;
            k++;
        }
        k = word.length()-1;
        while(word[k] != '1' && k>=0){
            borderRight++;
            k--;
        }
        int biggestDiff = 0, current = 0;
        for(int i=0;i<n;i++){
            if(word[i] == '0'){
                current++;
                biggestDiff = max(biggestDiff, current);
            }else{
                current = 0;
            }
        }
        cout << max(biggestDiff, borderLeft + borderRight) << endl;


    }


    return 0;
}