#include<bits/stdc++.h>
using namespace std;

void simplifica(long long& a, long long& b){
    int g = __gcd(a,b);
    a/=g; b/=g;
}

int main(){

    long long k, n;
    cin >> k >> n;
    long long quantParSeg = (1 << k);
    long long topo = quantParSeg;
    long long tempSubida = (2*quantParSeg) + quantParSeg;
    long long tempDesc = quantParSeg + (quantParSeg/2);
    long long tempTotal = tempDesc + tempSubida;

    n = n%tempTotal;
    long long newN = n%tempSubida;
    if(n == newN){
        long long degrausCompSubiu = newN/3;
        newN = newN % 3;
        
        degrausCompSubiu*=4;
        quantParSeg*=4;
        
        long long hor =0, vert =0;
        if(newN < 2 && newN != 0){
            vert = newN * 2;
            newN = 0;
        }else if(newN != 0){
            
            vert = 2;
            newN -= 2;

            if(newN!=0){
                hor = newN * 4;
            }
        }
        long long ansVertical = degrausCompSubiu+vert, ansHorizontal = degrausCompSubiu+hor;
        long long denVert = quantParSeg, denHor = quantParSeg;

        simplifica(ansHorizontal, denHor);
        simplifica(ansVertical, denVert);


        if(ansHorizontal == 0){
            cout << "0 ";
        }
        else if(denHor == 1){
            cout << ansHorizontal << " ";
        }else cout << ansHorizontal << "/" << denHor << " ";

        if(ansVertical == 0){
            cout << "0";
        }
        else if(denVert == 1){
            cout << ansVertical;
        }else cout << ansVertical << "/" << denVert << " ";
    }else{
        long long degrausCompSubiu = (newN*2)/3;
        newN = (newN*2) % 3;
        // newN /=2;
        
        degrausCompSubiu*=8;
        quantParSeg*=8;
        
        long long hor =0, vert =0;
        if(newN < 2 && newN != 0){
            hor = newN * 4;
            newN = 0;
        }else if(newN != 0){
            hor = 1;
            newN -= 2;
            if(newN!=0){
                vert = newN * 8;
            }
        }
        long long ansVertical = (quantParSeg) - (degrausCompSubiu+vert), ansHorizontal = (quantParSeg) - (degrausCompSubiu+hor);
        long long denVert = quantParSeg, denHor = quantParSeg;

        simplifica(ansHorizontal, denHor);
        simplifica(ansVertical, denVert);


        if(ansHorizontal == 0){
            cout << "0 ";
        }
        else if(denHor == 1){
            cout << ansHorizontal << " ";
        }else cout << ansHorizontal << "/" << denHor << " ";

        if(ansVertical == 0){
            cout << "0";
        }
        else if(denVert == 1){
            cout << ansVertical;
        }else cout << ansVertical << "/" << denVert << " ";
    }

    cout << endl;

    return 0;
}