#include <algorithm>
#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <random>

struct Info {
    int val;
    Info(int size, bool weak, bool lev, bool levsub) {
        val = (size << 3) + (levsub << 2) + (lev << 1) + weak;
    }
    int Size() {
        return val >> 3;
    }
    void SetSize(int size) {
        val = (size << 3) + (val & 7);
    }
    bool Weak() {
        return val & 1;
    }
    void SetWeak(int weak) {
        val -= (val & 1);
        val = val | weak;
    }
    bool ThisLevel() {
        return val & 2;
    }
    void SetThisLevel(int lev) {
        val -= (val & 2);
        val = val | (lev << 1);
    }
    bool ThisLevelSub() {
        return val & 4;
    }
    void SetThisLS(int lev) {
        val -= (val & 4);
        val = val | (lev << 2);
    }
};

struct Node {
    int value;
    unsigned long priority;
    int left;
    int right;
    int parent;
    Info info;
};

std::vector<Node> nodes;
std::vector<int> free_places;
int NewNode(const Node& node) {
    if (free_places.size()) {
        nodes[free_places.back()] = node;
        int res = free_places.back();
        free_places.pop_back();
        return res;
    } else {
        nodes.emplace_back(node);
        return static_cast<int>(nodes.size()) - 1;
    }
}

void DeleteNode(int ind) {
    free_places.push_back(ind);
}

struct Spasite {
    int beg;
    int end;
    Spasite(int beg_, int end_) : beg(beg_), end(end_) {
        if (beg > end) {
            std::swap(beg, end);
        }
    }
    bool operator<(const Spasite& za_chto) const {
        return std::make_tuple(beg, end) < std::make_tuple(za_chto.beg, za_chto.end);
    }
};

struct EulerLes {
    static std::mt19937 gen;
    std::vector<std::set<int>> weak_edges;
    std::map<Spasite, std::pair<int, int>> gde_rebro;
    std::vector<int> gde_vertex;
    explicit EulerLes(int num) : weak_edges(num), gde_vertex(num) {
        for (int i = 0; i < num; ++i) {
            gde_vertex[i] = nodes.size();
            nodes.emplace_back(Node{i, gen(), 0, 0, 0,
                                     Info{1, 0, 0, 0}});
        }
    }

    int Size(int node) const {
        return node ? nodes[node].info.Size() : 0;
    }

    bool LevelSub(int node) const {
        return node ? nodes[node].info.ThisLevelSub() : false;
    }

    bool WeakSub(int node) const {
        return node ? nodes[node].info.Weak() : false;
    }

    bool IsWeak(int node) const {
        return gde_vertex[nodes[node].value] == node &&
               weak_edges[nodes[node].value].size();
    }

    void Update(int node) const {
        if (nodes[node].left) {
            nodes[nodes[node].left].parent = node;
        }
        if (nodes[node].right) {
            nodes[nodes[node].right].parent = node;
        }
        nodes[node].info.SetSize(Size(nodes[node].left) + Size(nodes[node].right) + 1);
        nodes[node].info.SetThisLS(LevelSub(nodes[node].left) || LevelSub(nodes[node].right) ||
                                      nodes[node].info.ThisLevel());
        nodes[node].info.SetWeak(WeakSub(nodes[node].left) || WeakSub(nodes[node].right)
              || IsWeak(node));
    }

    int Merge(int left, int right) {
        if (!left || !right) {
            return left ? left : right;
        }
        if (nodes[left].priority > nodes[right].priority) {
            nodes[left].right = Merge(nodes[left].right, right);
            Update(left);
            nodes[left].parent = 0;
            return left;
        }
        nodes[right].left = Merge(left, nodes[right].left);
        Update(right);
        nodes[right].parent = 0;
        return right;
    }

    auto Split(int cur) {
        int left = nodes[cur].left;
        nodes[cur].left = 0;
        Update(cur);
        int right = cur;
        while (nodes[cur].parent) {
            if (cur == nodes[nodes[cur].parent].left) {
                cur = nodes[cur].parent;
                nodes[cur].left = right;
                right = cur;
                Update(right);
            } else {
                cur = nodes[cur].parent;
                nodes[cur].right = left;
                left = cur;
                Update(left);
            }
        }
        if (left) {
            nodes[left].parent = 0;
        }
        if (right) {
            nodes[right].parent = 0;
        }
        return std::make_tuple(left, right);
    }

    int GetRoot(int node) const {  //  O(logn)
        while (nodes[node].parent) {
            node = nodes[node].parent;
        }
        return node;
    }

    bool Connected(int fir, int sec) const {  //  O(logn)
        int first = gde_vertex[fir];
        int second = gde_vertex[sec];
        return GetRoot(first) == GetRoot(second);
    }

    void UpdateWeak(int vert) {  //  O(logn)
        int node = gde_vertex[vert];
        while (node) {
            nodes[node].info.SetWeak(WeakSub(nodes[node].left) ||
                   WeakSub(nodes[node].right) || IsWeak(node));
            node = nodes[node].parent;
        }
    }

    void AddWeak(int first, int second) {   // O(logn)
        weak_edges[first].insert(second);
        weak_edges[second].insert(first);
        UpdateWeak(first);
        UpdateWeak(second);
    }

    int First(int node) const {  //  O(logn)
        while (nodes[node].left) {
            node = nodes[node].left;
        }
        return node;
    }

    int Last(int node) const {  //  O(logn)
        while (nodes[node].right) {
            node = nodes[node].right;
        }
        return node;
    }

    int Next(int node) const {  //  O(logn)
        if (nodes[node].right) {
            return First(nodes[node].right);
        }
        while (nodes[nodes[node].parent].right == node) {
            node = nodes[node].parent;
        }
        return nodes[node].parent;
    }

    void GoUp(int node) {  // O(logn)
        while (node) {
            Update(node);
            node = nodes[node].parent;
        }
    }

    void MakeRoot(int node) {  //  O(logn)
        int root = GetRoot(node);
        int first = First(root);
        int last = Last(root);
        if (nodes[first].value == nodes[node].value) {
            return;
        }
        bool update = false;
        if (gde_vertex[nodes[last].value] == last) {
            gde_vertex[nodes[last].value] = first;
            update = true;
        }
        if (nodes[last].left) {
            nodes[nodes[last].left].parent = nodes[last].parent;
        }
        if (nodes[last].parent) {
            nodes[nodes[last].parent].right = nodes[last].left;
        }
        if (update) {
            int parent = nodes[last].parent;
            GoUp(parent);
            GoUp(first);
        }
        DeleteNode(last);
        auto [left, right] = Split(node);
        last = NewNode({nodes[node].value, gen(), 0, 0, 0,
                        Info{1, 0, false, 0}});
        Merge(Merge(right, left), last);
    }

    void AddEdge(int fir, int sec, bool this_level) {   //  log
        MakeRoot(gde_vertex[sec]);  //  log
        auto [left, right] = Split(gde_vertex[fir]);
        int first_insert = NewNode({fir, gen(), 0, 0, 0,
                           Info{1, 0, this_level, this_level}});
        left = Merge(Merge(left, first_insert), GetRoot(gde_vertex[sec]));
        int second_insert = Last(left);
        nodes[second_insert].info.SetThisLevel(this_level);
        gde_rebro[Spasite(fir, sec)] = std::make_pair(first_insert, second_insert);
        GoUp(second_insert);
        Merge(left, right);
    }

    bool HasWeakEdge(int first, int second) const {  //  O(1)
        return weak_edges[first].find(second) != weak_edges[first].end();
    }

    void DeleteWeak(int first, int second) {   //  log
        weak_edges[first].erase(second);
        weak_edges[second].erase(first);
        if (weak_edges[first].empty()) {
            UpdateWeak(first);
        }
        if (weak_edges[second].empty()) {
            UpdateWeak(second);
        }
    }

    void DeleteEdge(int first, int second) {   //  log
        auto res = gde_rebro[Spasite(first, second)];
        int fir = res.first;
        int sec = res.second;
        int next_f = Next(fir);
        gde_rebro.erase(Spasite(first, second));
        auto [left, right] = Split(next_f);
        int size = nodes[right].info.Size();
        int next = Next(sec);
        auto [nleft, nright] = Split(next);
        if (nodes[right].info.Size() == size) {
            int last = Last(nleft);
            bool no = false;
            if (nleft == last) {
                no = true;
            }
            if (gde_vertex[nodes[last].value] == last) {
                gde_vertex[nodes[last].value] = next_f;
                UpdateWeak(nodes[last].value);
            }
            if (nodes[last].parent) {
                nodes[nodes[last].parent].right = nodes[last].left;
            }
            if (nodes[last].left) {
                nodes[nodes[last].left].parent = nodes[last].parent;
            }
            GoUp(nodes[last].left);
            if (no) {
                nleft = nodes[last].left;
            }
            DeleteNode(last);
            last = Last(nright);
            nodes[last].info.SetThisLevel(false);
            GoUp(last);
            Merge(nleft, right);
        } else {
            int last = Last(left);
            bool no = false;
            if (last == left) {
                no = true;
            }
            if (gde_vertex[nodes[last].value] == last) {
                gde_vertex[nodes[last].value] = next;
                UpdateWeak(nodes[last].value);
            }
            if (nodes[last].parent) {
                nodes[nodes[last].parent].right = nodes[last].left;
            }
            if (nodes[last].left) {
                nodes[nodes[last].left].parent = nodes[last].parent;
            }
            GoUp(nodes[last].left);
            if (no) {
                left = nodes[last].left;
            }
            DeleteNode(last);
            last = Last(nleft);
            nodes[last].info.SetThisLevel(false);
            GoUp(last);
            Merge(left, nright);
        }
    }

    int Smaller(int fir, int sec) const {  //  log
        int first = gde_vertex[fir];
        int second = gde_vertex[sec];
        first = GetRoot(first);
        second = GetRoot(second);
        return nodes[first].info.Size() > nodes[second].info.Size() ? second : first;
    }

    void LowerLevel(int root, std::vector<std::pair<int, int>>& edges) {
        if (!LevelSub(root)) {
            return;
        }
        LowerLevel(nodes[root].left, edges);
        LowerLevel(nodes[root].right, edges);
        if (nodes[root].info.ThisLevel()) {
            edges.push_back({nodes[root].value, nodes[Next(root)].value});
            nodes[root].info.SetThisLevel(false);
        }
        nodes[root].info.SetThisLS(LevelSub(nodes[root].left) ||
                     LevelSub(nodes[root].right) || nodes[root].info.ThisLevel());
    }

    auto LowerLevel(int root) {
        std::vector<std::pair<int, int>> edges;
        LowerLevel(root, edges);
        return edges;
    }

    std::optional<std::pair<int, int>> SearchWeak(
            int root, std::vector<std::pair<int, int>>& edges) {
        if (!WeakSub(root)) {
            return std::nullopt;
        }
        auto res = SearchWeak(nodes[root].left, edges);
        if (res) {
            nodes[root].info.SetWeak(WeakSub(nodes[root].left) ||
                  WeakSub(nodes[root].right) || IsWeak(root));
            return res;
        }
        res = SearchWeak(nodes[root].right, edges);
        if (res) {
            nodes[root].info.SetWeak(WeakSub(nodes[root].left) ||
                   WeakSub(nodes[root].right) || IsWeak(root));
            return res;
        }
        std::vector<int> adj;
        for (int ad : weak_edges[nodes[root].value]) {
            adj.push_back(ad);
            edges.push_back({nodes[root].value, ad});
            if (GetRoot(gde_vertex[ad]) != GetRoot(gde_vertex[nodes[root].value])) {
                edges.pop_back();
                res.emplace(nodes[root].value, ad);
                break;
            }
        }
        for (int ad : adj) {
            weak_edges[nodes[root].value].erase(ad);
            weak_edges[ad].erase(nodes[root].value);
            if (weak_edges[ad].empty()) {
                GoUp(gde_vertex[ad]);
            }
        }
        nodes[root].info.SetWeak(WeakSub(nodes[root].left) ||
                   WeakSub(nodes[root].right) || IsWeak(root));
        return res;
    }

    auto SearchWeak(int root) {
        std::vector<std::pair<int, int>> edges;
        auto mmm = SearchWeak(root, edges);
        return std::make_tuple(edges, mmm);
    }
};

std::mt19937 EulerLes::gen(6663315);

class DynamicGraph {
private:
    int log_;
    std::vector<EulerLes> stroitelnie_lesa_;
    int Log(int num) {
        int res = 0;
        int pwr = 1;
        while (pwr < num) {
            pwr <<= 1;
            ++res;
        }
        return res;
    }
    int size_;

public:
    explicit DynamicGraph(int num)
            : log_(Log(num)), size_(num) {
        stroitelnie_lesa_.reserve(log_);
        NewNode(Node{0, 0, 0, 0, 0, Info{0, 0, 0, 0}});
        for (int i = 0; i < log_; ++i) {
            stroitelnie_lesa_.emplace_back(num);
        }
    }

    int GetComponentsNumber() const {
        return size_;
    }

    void AddEdge(int first, int second) {
        if (stroitelnie_lesa_.back().Connected(first, second)) {
            stroitelnie_lesa_.back().AddWeak(first, second);
        } else {
            --size_;
            stroitelnie_lesa_.back().AddEdge(first, second, true);
        }
    }

    void RemoveEdge(int first, int second) {
        int level = 0;
        for (; level < log_; ++level) {
            if (stroitelnie_lesa_[level].HasWeakEdge(first, second)) {
                stroitelnie_lesa_[level].DeleteWeak(first, second);
                return;
            }
            if (stroitelnie_lesa_[level].gde_rebro.find(Spasite(first, second)) !=
                stroitelnie_lesa_[level].gde_rebro.end()) {
                break;
            }
        }
        std::optional<std::pair<int, int>> god_exists;
        for (; level < log_; ++level) {
            stroitelnie_lesa_[level].DeleteEdge(first, second);
            int smaller = stroitelnie_lesa_[level].Smaller(first, second);
            auto lower_list = stroitelnie_lesa_[level].LowerLevel(smaller);
            for (auto& pair : lower_list) {
                if (pair.first < pair.second) {
                    stroitelnie_lesa_[level - 1].AddEdge(pair.first, pair.second, true);
                }
            }
            if (god_exists) {
                stroitelnie_lesa_[level].AddEdge(god_exists->first, god_exists->second, false);
            } else {
                auto [weak_list, god] = stroitelnie_lesa_[level].SearchWeak(smaller);
                for (auto& pair: weak_list) {
                    if (!stroitelnie_lesa_[level - 1].HasWeakEdge(pair.first, pair.second)) {
                        stroitelnie_lesa_[level - 1].AddWeak(pair.first, pair.second);
                    }
                }
                if (god) {
                    stroitelnie_lesa_[level].AddEdge(god->first, god->second, true);
                    god_exists = god;
                }
            }
        }
        if (!god_exists) {
            ++size_;
        }
    }
};
