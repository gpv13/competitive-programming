#include<bits/stdc++.h>
using namespace std;

//memo[idx][cnt][jaComecouAConst][isUnder]
long long memo[20][20][2][2];

long long solve(string s, int idx, int cnt, int jaComecouAConst, int isUnder, int num){

    if(memo[idx][cnt][jaComecouAConst][isUnder] != -1) return memo[idx][cnt][jaComecouAConst][isUnder];
    if(idx == s.size()){
        if(cnt >= s.size()/2) return 1;
        else return 0;
    }

    long long ans = 0;
    int limit = isUnder ? 9 : (s[idx] - '0');


    for(int d=0;d<=limit;d++){
        int newJaComecouAConst = jaComecouAConst || (d!=0);
        int newIsUnder = isUnder || (d < limit);
        if(!d && jaComecouAConst) ans+= solve(s, idx+1, cnt + (d == num ? 1 : 0), newJaComecouAConst, newIsUnder, num);
        else if(d) ans += solve(s, idx+1, cnt + (d == num ? 1 : 0), newJaComecouAConst, newIsUnder, num);
    }

    return memo[idx][cnt][jaComecouAConst][isUnder] = ans;
}

void reset(){
    for(int i=0;i<19;i++)
        for(int j=0;j<19;j++)
            for(int k=0;k<2;k++)
                for(int l=0;l<2;l++)
                    memo[i][j][k][l] = -1;
}

int main(){

    string xs, y;
    long long int x;
    cin >> x >> y;
    x--;
    xs = to_string(x);
    long long resp = 0;
    for(int i=0;i<=9;i++){
        reset();
        resp += (solve(y, 0, 0, 0, 0, i) - solve(xs, 0, 0, 0, 0, i));   
    }
    cout << resp << endl;


    return 0;
}