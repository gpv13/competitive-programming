#include <bits/stdc++.h>

using namespace std;

// Estrutura para representar uma aresta ponderada
struct Aresta {
    int u, v, peso;

    // Operador para permitir a ordenação das arestas pelo peso
    bool operator<(const Aresta& other) const {
        return peso < other.peso;
    }
};

// --- Estrutura Union-Find (DSU) ---
vector<int> pai;
vector<int> tamanho;

// Encontra o representante do conjunto de 'i' com compressão de caminho
int find(int i) {
    if (pai[i] == i) {
        return i;
    }
    return pai[i] = find(pai[i]);
}

// Une os conjuntos de 'a' e 'b' por tamanho
void unite(int a, int b) {
    a = find(a);
    b = find(b);
    if (a != b) {
        if (tamanho[a] < tamanho[b]) {
            swap(a, b);
        }
        pai[b] = a;
        tamanho[a] += tamanho[b];
    }
}
// --- Fim da Estrutura Union-Find ---


// Função principal do Algoritmo de Kruskal
long long kruskal(int n, vector<Aresta>& arestas) {
    // Inicializa a estrutura Union-Find
    pai.resize(n);
    iota(pai.begin(), pai.end(), 0); // Preenche pai[i] = i
    tamanho.assign(n, 1);

    // 1. Ordena todas as arestas pelo peso
    sort(arestas.begin(), arestas.end());

    long long custo_total = 0;
    vector<Aresta> mst_arestas;

    // 2. Percorre as arestas ordenadas
    for (const auto& aresta : arestas) {
        // 3. Verifica se os vértices da aresta estão em componentes diferentes
        if (find(aresta.u) != find(aresta.v)) {
            // Se sim, a aresta não forma um ciclo
            custo_total += aresta.peso;
            mst_arestas.push_back(aresta);
            unite(aresta.u, aresta.v);
        }
    }

    // Opcional: Verificar se uma MST foi formada (todos os vértices conectados)
    // if (mst_arestas.size() != n - 1) {
    //     return -1; // Grafo não é conexo
    // }

    return custo_total;
}
int main(){

    
    


    return 0;
}