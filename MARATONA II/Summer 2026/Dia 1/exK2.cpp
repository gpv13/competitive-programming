#include<bits/stdc++.h>
using namespace std;

struct Monstro {
    int id;
    int atk, def;
};

// Criamos uma struct para comparar os iteradores pelo ID do monstro
struct ComparaIterador {
    bool operator()(const list<Monstro>::iterator& a, const list<Monstro>::iterator& b) const {
        return a->id < b->id;
    }
};

int main(){
    ios::sync_with_stdio(0); cin.tie(0);

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        vector<int> atk(n), def(n);
        for(int i=0; i<n; i++) cin >> atk[i];
        for(int i=0; i<n; i++) cin >> def[i];

        list<Monstro> stats;
        for(int i = 0; i < n; i++){
            stats.push_back({i, atk[i], def[i]});
        }

        // Agora o set usa a struct ComparaIterador
        set<list<Monstro>::iterator, ComparaIterador> candidatos;

        for(auto it = stats.begin(); it != stats.end(); it++){
            candidatos.insert(it);
        }

        for(int r = 0; r < n; r++){
            set<list<Monstro>::iterator, ComparaIterador> mortos_da_vez;
            set<list<Monstro>::iterator, ComparaIterador> proximos;

            for(auto it : candidatos){
                long long dano = 0;
                if(it != stats.begin()) dano += prev(it)->atk;
                if(next(it) != stats.end()) dano += next(it)->atk;

                if(dano > it->def){
                    mortos_da_vez.insert(it);
                }
            }

            cout << mortos_da_vez.size() << (r == n-1 ? "" : " ");

            if(mortos_da_vez.empty()){
                for(int i = r + 1; i < n; i++) cout << "0" << (r == n-1 ? "" : " ");
                break;
            }

            for(auto it : mortos_da_vez){
                if(it != stats.begin()) proximos.insert(prev(it));
                if(next(it) != stats.end()) proximos.insert(next(it));
            }

            for(auto it : mortos_da_vez){
                proximos.erase(it);
                stats.erase(it);
            }

            candidatos = proximos; // Agora isso funciona perfeitamente!
        }
        cout << endl;
    }
    return 0;
}