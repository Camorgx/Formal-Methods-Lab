import numpy as np


class Graph:
    def __init__(self):
        self.n = 17
        self.d = np.full((self.n, self.n), dtype=int, fill_value=1024)
        self.pi = np.full((self.n, self.n), dtype=int, fill_value=-1)
        self.edges = [(i, i + 1) for i in range(1, 16)]
        self.edges += [(4, 6), (8, 10), (16, 1), (16, 2)]
        tmp = [3, 7, 11, 15]
        for node in tmp:
            self.edges += [(node, 17), (17, node)]
        for edge in self.edges:
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
                        self.pi[i, j] = self.pi[k, j]

    def add_edge(self, frm: int, to: int):
        self.d[frm - 1, to - 1] = 1
        self.pi[frm - 1, to - 1] = frm - 1


graph = Graph()
process_cnt = graph.n
channel_cnt = len(graph.edges)


def first_hop_in_shortest_path(n: int, m: int) -> int:
    n -= 1
    m -= 1
    to = m
    frm = graph.pi[n, m]
    while frm != -1 and frm != n:
        to = frm
        frm = graph.pi[n, frm]
    return -1 if frm == -1 else to + 1


def ok(n: int, m: int, frm: int, to: int) -> bool:
    return frm == n and to == first_hop_in_shortest_path(n, m)


def generate_code() -> str:
    c = [f'c{i}' for i in range(1, channel_cnt + 1)]
    res = "MODULE main\nVAR\n"
    for i in range(channel_cnt):
        res += f'    {c[i]}: 0..{process_cnt};\n'
    res += 'INIT\n'
    init = [f'({c[i]} = 0)' for i in range(channel_cnt)]
    res += '    (' + '\n    & '.join(init) + ')'
    return res


def main():
    print(first_hop_in_shortest_path(1, 16))


if __name__ == '__main__':
    main()
