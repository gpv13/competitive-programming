#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    for(int k =0;k<t;k++){

        string num;
        cin >> num;

        int intnum = 0;

        intnum += (((num[0] - '0') * 1000) + ((num[1] - '0') * 100) + ((num[2] - '0') * 10) + num[3] - '0');
        int raiz = sqrt(intnum);
        if(raiz*raiz == intnum) cout << "0 " << raiz << endl;
        else cout << "-1" << endl;

    }


    return 0;
}