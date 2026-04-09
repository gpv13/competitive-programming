#include <bits/stdc++.h>
using namespace std;

//k escolhe 3 -> (k 3) -> k! / 3! (k-3)! -> (k * k-1 * k-2)/6


int main()
{

    int n, k;
    cin >> n >> k;

    vector<long long> F(1 << k, 0);
    vector<long long> A(1<<k, 0);
    for (int i = 0; i < n; i++)
    {
        string s;
        cin >> s;
        long long int mask = 0;
        for (int i = 0; i < k; i++)
        {
            mask += s[i] == '0' ? 0 : (1 << k - i - 1);
        }
        A[mask]++;
    }

    // for(int i=0;i<A.size();i++){
    //     cout << A[i] << " ";
    // }
    for (int i = 0; i < (1 << k); ++i)
        F[i] = A[i];
    for (int i = 0; i < k; ++i)
        for (int mask = 0; mask < (1 << k); ++mask)
        {
            if (mask & (1 << i))
                F[mask] += F[mask ^ (1 << i)];
        }


    for(int i=0;i<(1<<k);i++){
        long long maior = F[i];
        if(F[i] < 3){
            F[i] = 0;
        }else{
            F[i] = (maior*(maior-1)*(maior-2))/6;
        }
    }

    for (int i = 0; i < k; ++i)
        for (int mask = 0; mask < (1 << k); ++mask)
        {
            if (mask & (1 << i))
                F[mask] -= F[mask ^ (1 << i)];
        }

    int q;
    cin >> q;
    while(q--){
        string s;
        cin >> s;
        long long int mask = 0;
        for (int i = 0; i < k; i++)
        {
            mask += s[i] == '0' ? 0 : (1 << k - i - 1);
        }
        cout << F[mask] << endl;
    }

}