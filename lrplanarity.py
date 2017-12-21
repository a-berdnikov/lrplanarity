from collections import defaultdict, deque
import itertools

INF = float('inf')


class Interval:
    def __init__(self, low=None, high=None):
        self.low = low
        self.high = high

    def is_empty(self):
        return self.low == self.high == None


class Conflict_pair:
    def __init__(self, L=None, R=None):
        self.L = L if L is not None else Interval()
        self.R = R if R is not None else Interval()


class Not_planar_error(Exception):
    pass

def constant_factory(value):
    return lambda: value

def linear_sort(lst, key):
    keys = [key(v) for v in lst]
    max_key, min_key = max(keys), min(keys)
    sorted_parts = [[] for _ in range(max_key-min_key+1)]
    for v, k in zip(lst, keys):
        sorted_parts[k-min_key].append(v)
    return list_chain(sorted_parts)

def list_chain(iterable):
    return list(itertools.chain.from_iterable(iterable))


class Planarity_solver:
    def __init__(self, graph):
        self.graph = graph
        self.roots = []
        self.dfs_graph = defaultdict(list)
        self.parent_edge = defaultdict(constant_factory(None))

        self.height = defaultdict(constant_factory(INF))
        self.lowpt = {}
        self.lowpt2 = {}
        self.nesting_depth = {}

        self._orient()

        self.ref = defaultdict(constant_factory(None))
        self.side = defaultdict(constant_factory(1))
        self.S = [None]
        self.stack_bottom = {}
        self.lowpt_edge = {}

        self.embedded_graph = {}

    def _orient(self):
        for s in self.graph:
            if self.height[s] == INF:
                self.height[s] = 0
                self.roots.append(s)
                self._dfs1(s)

    def _test(self):
        self._sort_adjacency_lists()
        for s in self.roots:
            self._dfs2(s)

    def _embed(self):
        for v, adjacency_list in self.dfs_graph.items():
            for w in adjacency_list:
                e = v, w
                self.nesting_depth[e] *= self._sign(e)
        self._sort_adjacency_lists()
        for s in self.roots:
            self.embedded_graph[s] = [[]]
            self._dfs3(s)

    def _dfs1(self, v):
        e = self.parent_edge[v]
        for w in self.graph[v]:
            if self.height[v]-1 <= self.height[w] < INF:
                continue

            self.dfs_graph[v].append(w)
            self.lowpt[v, w] = self.lowpt2[v, w] = self.height[v]
            if self.height[w] == INF:
                self.parent_edge[w] = v, w
                self.height[w] = self.height[v] + 1
                self._dfs1(w)
            else:
                self.lowpt[v, w] = self.height[w]

            self.nesting_depth[v, w] = 2 * self.lowpt[v, w] + (self.lowpt2[v, w] < self.height[v])

            # Update lowpoints of parent edge e.
            if e is not None:
                if self.lowpt[v, w] < self.lowpt[e]:
                    self.lowpt2[e] = min(self.lowpt[e], self.lowpt2[v, w])
                    self.lowpt[e] = self.lowpt[v, w]
                elif self.lowpt[v, w] > self.lowpt[e]:
                    self.lowpt2[e] = min(self.lowpt2[e], self.lowpt[v, w])
                else:
                    self.lowpt2[e] = min(self.lowpt2[e], self.lowpt2[v, w])

    def _dfs2(self, v):
        e = self.parent_edge[v]
        for i, w in enumerate(self.dfs_graph[v]):
            e_i = v, w
            self.stack_bottom[e_i] = self.S[-1]
            if e_i == self.parent_edge[w]:
                self._dfs2(w)
            else:
                self.lowpt_edge[e_i] = e_i
                self.S.append(Conflict_pair(R=Interval(e_i, e_i)))

            # Integrate new return edges.
            if self.lowpt[e_i] < self.height[v]:
                if i == 0:
                    self.lowpt_edge[e] = self.lowpt_edge[e_i]
                else: # Add constraints of e_i.
                    P = Conflict_pair()

                    # Merge return edges of e_i into P.R.
                    while self.S[-1] != self.stack_bottom[e_i]:
                        Q = self.S.pop()
                        if not Q.L.is_empty():
                            if not Q.R.is_empty():
                                raise Not_planar_error()
                            Q = Conflict_pair(Q.R, Q.L)
                        if self.lowpt[Q.R.low] > self.lowpt[e]:
                            if P.R.is_empty():
                                P.R.high = Q.R.high
                            else:
                                self.ref[P.R.low] = Q.R.high
                            P.R.low = Q.R.low
                        else:
                            self.ref[Q.R.low] = self.lowpt_edge[e]

                    # Merge conflicting return edges of e_1, ..., e_(i-1) into P.L.
                    while self._conflicting(self.S[-1].L, e_i) or self._conflicting(self.S[-1].R, e_i):
                        Q = self.S.pop()
                        if self._conflicting(Q.R, e_i):
                            if self._conflicting(Q.L, e_i):
                                raise Not_planar_error()
                            Q = Conflict_pair(Q.R, Q.L)

                        self.ref[P.R.low] = Q.R.high
                        if Q.R.low is not None:
                            P.R.low = Q.R.low

                        if P.L.is_empty():
                            P.L.high = Q.L.high
                        else:
                            self.ref[P.L.low] = Q.L.high
                        P.L.low = Q.L.low

                    if P != Conflict_pair():
                        self.S.append(P)

        if e is not None:
            u = e[0]

            # Trim back edges ending at parent u: 2 steps.

            # Step 1: drop entire conflict pairs.
            while self.S[-1] is not None and self._lowest(self.S[-1]) == self.height[u]:
                P = self.S.pop()
                if P.L.low is not None:
                    self.side[P.L.low] = -1

            # Step 2: consider one more conflict pair.
            if self.S[-1] is not None:
                P = self.S.pop()

                # Trim left interval.
                while P.L.high is not None and P.L.high[1] == u:
                    P.L.high = self.ref[P.L.high]
                if P.L.high is None and P.L.low is not None:
                    self.ref[P.L.low] = P.R.low
                    self.side[P.L.low] = -1
                    P.L.low = None

                # Trim right interval.
                while P.R.high is not None and P.R.high[1] == u:
                    P.R.high = self.ref[P.R.high]
                if P.R.high is None and P.R.low is not None:
                    self.ref[P.R.low] = P.L.low
                    self.side[P.R.low] = -1
                    P.R.low = None

                self.S.append(P)

            # Side of e is side of the highest return edge (left or right).
            if self.lowpt[e] < self.height[u]:
                h_L, h_R = self.S[-1].L.high, self.S[-1].R.high
                if h_L is not None and (h_R is None or self.lowpt[h_L] > self.lowpt[h_R]):
                    self.ref[e] = h_L
                else:
                    self.ref[e] = h_R

    def _dfs3(self, v):
        for w in self.dfs_graph[v]:
            e_i = v, w
            if e_i == self.parent_edge[w]:
                self.embedded_graph[w] = [[v]]
                self.embedded_graph[v].append(deque([w]))
                self.embedded_graph[v].append(deque())
                self._dfs3(w)
            else:
                if self.side[e_i] == 1:
                    self.embedded_graph[w][-1].appendleft(v)
                else:
                    self.embedded_graph[w][-2].appendleft(v)
                self.embedded_graph[v][-1].append(w)
        self.embedded_graph[v] = list_chain(self.embedded_graph[v])

    def _sort_adjacency_lists(self):
        self.dfs_graph = {v : linear_sort(adjacency_list, lambda w: self.nesting_depth[v, w])
                              for v, adjacency_list in self.dfs_graph.items()}

    def _conflicting(self, I, b):
        return not I.is_empty() and self.lowpt[I.high] > self.lowpt[b]
    
    def _lowest(self, P):
        if P.L.is_empty():
            return self.lowpt[P.R.low]
        if P.R.is_empty():
            return self.lowpt[P.L.low]
        return min(self.lowpt[P.L.low], self.lowpt[P.R.low])

    def _sign(self, e):
        if self.ref[e] is not None:
            self.side[e] *= self._sign(self.ref[e])
            self.ref[e] = None
        return self.side[e]

    def is_planar(self):
        try:
            self._test()
            return True
        except Not_planar_error:
            return False

    def embed(self):
        self._test()
        self._embed()
        return self.embedded_graph


def is_planar(graph):
    return Planarity_solver(graph).is_planar()

def embed(graph):
    return Planarity_solver(graph).embed()
