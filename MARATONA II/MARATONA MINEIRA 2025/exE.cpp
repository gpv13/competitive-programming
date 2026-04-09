#include<bits/stdc++.h>

using namespace std;

#define MAXN 200100

int pai[MAXN]; // crio o vetor que armazenará os pais

// função find: retorna o patriarca de um elemento x
int find(int x){ 
	
	// se ele for pai de si mesmo, ele é o patriarca
	if(pai[x]==x) return x;
	
	// se não, devo olhar o patriarca de seu pai
	return find(pai[x]);
}

// função join: faz a união dos conjuntos dos elementos x e y
void join(int x, int y){
	
	// basta fazer o patriarca de um se tornar pai do patriarca do outro
	pai[find(x)]=find(y);
}

int main(){


    int n;
    cin >> n;
    for(int i=1; i<=n; i++) pai[i]=i;
    vector<int> tamCiclo(n+1, 0);
    for(int i=0;i<n;i++){
        int d, q;
        cin >> d >> q;
        join(d, q);
    }
    for(int i=1;i<=n;i++){
        tamCiclo[find(i)]++;
    }
    int total = 0;
    for(int i=1;i<=n;i++){
        if(tamCiclo[i] > 0) total += tamCiclo[i] - 1; 
    }
    cout << total << endl;

    return 0;
}