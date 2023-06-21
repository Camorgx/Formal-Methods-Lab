import numpy as np


class Edge:
    def __init__(self, frm: int, to: int, index: int):
        self.frm = frm
        self.to = to
        self.index = index


class Graph:
    def __init__(self, n: int, edges: list):
        self.n = n
        self.d = np.full((self.n, self.n), dtype=int, fill_value=1024)
        self.hop = np.full((self.n, self.n), dtype=int, fill_value=-1)
        self.edges_index = dict()
        self.edges = []
        self.edge_cnt = 0

        for edge in edges:
            self.add_edge(edge[0], edge[1])
        for i in range(self.n):
            self.d[i, i] = 0
        self.floyd()

    def floyd(self):
        for k in range(self.n):
            for i in range(self.n):
                for j in range(self.n):
                    if self.d[i, j] > self.d[i, k] + self.d[k, j]:
                        self.d[i, j] = self.d[i, k] + self.d[k, j]
                        self.hop[i, j] = self.hop[i, k]

    def add_edge(self, frm: int, to: int):
        self.d[frm - 1, to - 1] = 1
        self.hop[frm - 1, to - 1] = to - 1
        self.edge_cnt += 1
        self.edges.append(Edge(frm, to, self.edge_cnt))
        self.edges_index[(frm, to)] = self.edge_cnt

    def get_index(self, frm: int, to: int):
        return self.edges_index[(frm, to)]


process_cnt = 17
edge_list = [(i, i + 1) for i in range(1, 16)]
edge_list += [(4, 6), (8, 10), (16, 1), (16, 2)]
mute = [3, 7, 11, 15]
for edg in mute:
    edge_list += [(edg, 17), (17, edg)]

graph = Graph(process_cnt, edge_list)
channel_cnt = graph.edge_cnt
Q = []


def first_hop_in_shortest_path(n: int, m: int) -> int:
    return graph.hop[n - 1, m - 1] + 1


# 需要枚举 M 中节点所有两两组合的可能情况
def send(n: int, m: int) -> str:
    hop = first_hop_in_shortest_path(n, m)
    index = graph.get_index(n, hop)
    edge = f'c{index}'
    Q.append(f'({edge} = 0)')
    res = f'(case {edge} = 0 : next({edge}) = {m}; TRUE : next({edge}) = {edge}; esac)\n        '
    res = [res]
    for e in graph.edges:
        if index != e.index:
            res.append(f'(next(c{e.index}) = c{e.index})')
    return '(' + ' & '.join(res) + ')'


# 需要枚举每条指向 M 中节点的边
def receive(index: int) -> str:
    edge = f'c{index}'
    m = graph.edges[index - 1].to
    Q.append(f'({edge} = {m})')
    res = f'(case {edge} = {m} : next({edge}) = 0; TRUE : next({edge}) = {edge}; esac)\n        '
    res = [res]
    for e in graph.edges:
        if index != e.index:
            res.append(f'(next(c{e.index}) = c{e.index})')
    return '(' + ' & '.join(res) + ')'


M = [2, 4, 6]
# M = [1, 5, 9, 13]


# 需要枚举每条边
def process(index: int) -> str:
    c1 = f'c{index}'
    n = graph.edges[index - 1].to
    res = []
    for m in M:
        hop = first_hop_in_shortest_path(n, m)
        if hop == 0:
            continue
        c2_index = graph.edges_index[(n, hop)]
        c2 = f'c{c2_index}'
        Q.append(f'(({c1} = {m}) & ({c2} = 0))')
        tmp = f'(case ({c1} = {m}) & ({c2} = 0) : (next({c1}) = 0) & (next({c2}) = {m}); ' \
              f'TRUE : next({c1}) = {c1} & next({c2}) = {c2}; esac)\n        '
        tmp = [tmp]
        for e in graph.edges:
            if e.index != index and e.index != c2_index:
                tmp.append(f'(next(c{e.index}) = c{e.index})')
        tmp = ' & '.join(tmp)
        res.append(f'({tmp})')
    return '\n    | '.join(res)


def generate_code() -> str:
    c = [f'c{i}' for i in range(1, channel_cnt + 1)]
    res = "MODULE main\nVAR\n"
    for i in range(channel_cnt):
        res += f'    {c[i]}: 0..{process_cnt};\n'
    res += 'INIT\n'
    init = [f'({c[i]} = 0)' for i in range(channel_cnt)]
    res += '    (' + ' & '.join(init) + ')\n'
    res += 'TRANS (\n    '
    trans = []
    for sender in M:
        for receiver in M:
            if sender != receiver:
                trans.append(send(sender, receiver))
    for node in M:
        edges = []
        for edge in graph.edges:
            if edge.to == node:
                edges.append(edge.index)
        for edge in edges:
            trans.append(receive(edge))
    for edge in graph.edges:
        trans.append(process(edge.index))
    res += '\n    | '.join(trans)
    res += '\n)\n'
    res += 'CTLSPEC !(EF !(\n    ' + '\n    | '.join(Q) + '\n))\n'
    return res


def main():
    for edge in graph.edges:
        print(f'index = {edge.index}, from = {edge.frm}, to = {edge.to}')
    with open('deadlock.smv', 'w') as file:
        file.write(generate_code())


if __name__ == '__main__':
    main()
