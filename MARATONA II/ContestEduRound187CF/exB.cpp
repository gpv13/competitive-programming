#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >>t;
    while(t--){
        string s;
        cin >> s;
        int somatot = 0;
        vector<int> nums(10,0);
        for(int i=0;i<s.size();i++) {
            somatot+=s[i]-'0';
            if(i) nums[s[i]-'0']++;
            else nums[s[i]-'0'-1]++;
        }
        int op = 0;
        int auxpos = 9;
        while(somatot >= 10){

            while(nums[auxpos] == 0) auxpos--;
            nums[auxpos]--;
            somatot-=auxpos;
            op++;

        }
        cout << op << endl;

    }

    return 0;
}