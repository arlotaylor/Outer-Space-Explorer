from tkinter import *
from random import randint
from math import sqrt, cos, sin, pi
from copy import deepcopy



def comp(x,n):
    return x ^ (2**(2*n)-1)

def intersect(x,y):
    return x & y

def isCompatible(x,y,n):
    return 0 in [intersect(x,y),intersect(comp(x,n),y),intersect(x,comp(y,n)),intersect(comp(x,n),comp(y,n))]


def isIdeal(x,n):
    if x.bit_count() <= 1 or x.bit_count() >= 2*n-1:
        return False
    mask = int((1 - 4**n)/(-3))
    return ((x & mask) << 1) != (x & (mask << 1))

def generateIdealEdges(n):
    ret = []
    x = 1
    while x < 2**(2*n):
        if isIdeal(x,n):
            ret.append(x)
        x += 2
    return ret

def iterateIdeals(prev,eds,n,spare=False):
    ret = []
    for i in prev:
        for j in eds[0 if spare else (eds.index(i[-1])+1):]:
            for k in i:
                if k == j or not isCompatible(k,j,n):
                    break
            else:
                ret.append(i + [j])
    return ret

def generateStar(n, start = None):
    ed = generateIdealEdges(n)
    prev = [[i] for i in generateIdealEdges(n)] if start is None else start
    ret = [[[]]] if start is None else []
    print(ret)
    while len(prev) != 0:
        print(len(prev))
        ret.append(prev)
        if start is None:
            prev = iterateIdeals(prev,ed,n)
        else:
            prev = iterateIdeals(prev,ed,n,True)
            start = None
    return ret



def getEquivalenceClasses(lst, lam):
    ret = []
    while lst:
        newEq = [0]
        for i in range(1,len(lst)):
            if lam(lst[0], lst[i]):
                newEq.append(i)
                
        ret.append([lst[i] for i in newEq])
        
        for i in reversed(newEq):
            lst.pop(i)
    return ret


class Word:
    def __init__(self, ls):
        i = 0
        while i < len(ls) - 1:
            if -1-ls[i] == ls[i+1]:
                ls = ls[:i] + ls[i+2:]
                if i > 0:
                    i -= 1
            else:
                i += 1
        self.ls = ls

    def __eq__(self, other):
        return self.ls == other.ls

    def rot(self):
        return Word([self.ls[-1]] + self.ls[:-1]) if self.ls else Word([])

    def inn(self, n=None):
        r = self.rot()
        for _ in self.ls if n is None else range(n):
            r = r.rot()
        return r

    def innEq(self, other):
        r1 = self.inn()
        r2 = other.inn()
        for _ in self.ls:
            if r1 == r2:
                return True
            r1 = r1.rot()
        return False


class Edge:
    def __init__(self, ls, rev=False):
        self.ls = ls
        self.rev = rev

    def __getitem__(self, it):
        return self.ls[-1-it if self.rev else it]

    def __setitem__(self, it, val):
        self.ls[-1-it if self.rev else it] = val


class Graph:
    def __init__(self, verts, edges):
        self.verts = verts
        self.edges = edges

    def __getitem__(self, it):
        return Edge(self.edges[it]) if it >= 0 else Edge(self.edges[-1-it], True)

    def getPaths(self, base, tree):
        ret = {base: []}
        ex = []
        while len(ret) < self.verts:
            for i in tree:
                if i in ex: continue
                if self.edges[i][0] in ret:
                    ret[self.edges[i][1]] = ret[self.edges[i][0]] + [i]
                    ex.append(i)
                elif self.edges[i][1] in ret:
                    ret[self.edges[i][0]] = ret[self.edges[i][1]] + [-1-i]
                    ex.append(i)
        return ret

    def getEdgesTo(self, v):
        return [k for k in range(-len(self.edges),len(self.edges)) if self[k][1] == v]
        

    def collapseEdge(self, e):
        x = sorted(self.edges[e])
        return Graph(self.verts - 1, [[x[0] if n == x[1] else (n-1 if n > x[1] else n) for n in self.edges[i]]
                                      for i in range(len(self.edges)) if i != e])
        

    def expandVertex(self, v, e):
        ng = Graph(self.verts + 1, deepcopy(self.edges) + [[v,self.verts]])
        for i in e:
            ng[i][1] = self.verts
        return ng


def incrementSeq(ind, dic):
    for j in range(1,len(ind)):
        if dic[ind[j]] > min([dic[ind[k]] for k in range(j)]):
            m = max([dic[ind[k]] for k in range(j) if dic[ind[k]] < dic[ind[j]]])
            r = sorted([dic[ind[k]] for k in range(j+1) if dic[ind[k]] != m])
            for k in range(j):
                dic[ind[k]] = r[k]
            dic[ind[j]] = m
            return True

    r = sorted([dic[k] for k in ind])
    for k in range(len(ind)):
        dic[ind[k]] = r[k]
    return False


class GraphSymmetry:
    def __init__(self, graph):
        self.graph = graph
        degs = [sum([j.count(i) for j in graph.edges]) for i in range(graph.verts)]
        self.degs = degs
        self.ndegs = [{j:[graph.edges.count([i,j])+graph.edges.count([j,i]), degs[j]]
                  for j in range(graph.verts) if j != i and ([i,j] in graph.edges or [j,i] in graph.edges)}
                 for i in range(graph.verts)]
        eqclass = {}
        classcount = 0
        for i in range(graph.verts):
            for j in range(i):
                if degs[i] == degs[j] and sorted(list(self.ndegs[i].values())) == sorted(list(self.ndegs[j].values())):
                    eqclass[i] = eqclass[j]
                    break
            else:
                eqclass[i] = classcount
                classcount += 1

        self.vertclasses = [[j for j in eqclass if eqclass[j] == i] for i in range(classcount)]
        self.vertclasses = [sorted(i) for i in self.vertclasses if len(i) > 1]

        eqclass = {}
        classcount = 0
        for i in range(len(graph.edges)):
            for j in range(i):
                if graph.edges[i] == graph.edges[j]:
                    eqclass[i] = eqclass[j]
                    break
                elif list(reversed(graph.edges[i])) == graph.edges[j]:
                    eqclass[-1-i] = eqclass[j]
                    break
            else:
                eqclass[i] = classcount
                classcount += 1

        self.edgeclasses = [[j for j in eqclass if eqclass[j] == i] for i in range(classcount)]
        #print(self.edgeclasses)
        self.edgeclasses = [sorted(i) for i in self.edgeclasses if len(i) > 1]

        #print(self.edgeclasses)
        
        self.start = True

    def __iter__(self):
        self.vertmap = {i:i for i in range(self.graph.verts)}
        self.edgemap = {i:i for i in sum(self.edgeclasses,start=[])}
        self.start = True
        return self

    def __next__(self):
        if self.start:
            self.start = False
            return self

        for i in self.edgeclasses:
            if incrementSeq(i, self.edgemap):
                return self
        
        while True:
            for i in self.vertclasses:
                if incrementSeq(i, self.vertmap):
                    break
            else:
                raise StopIteration

            if False not in [False not in [self.vertmap[j] in self.ndegs[self.vertmap[i]] and self.ndegs[self.vertmap[i]][self.vertmap[j]] == self.ndegs[i][j] for j in self.ndegs[i]] for i in range(self.graph.verts)]:
                break
        return self

    def getMaps(self):
        ec = sum(self.edgeclasses,start=[])
        ecmap = {}
        for i in range(len(self.edgeclasses)):
            newEdge = [self.vertmap[self.graph[self.edgeclasses[i][0]][0]],self.vertmap[self.graph[self.edgeclasses[i][0]][1]]]
            if newEdge in self.graph.edges:
                ne = self.graph.edges.index(newEdge)
            else:
                ne = -1-self.graph.edges.index(list(reversed(newEdge)))
            if True in [ne in k for k in self.edgeclasses]:
                ecmap[i] = [ne in k for k in self.edgeclasses].index(True)
            else:
                ecmap[i] = -1-[-1-ne in k for k in self.edgeclasses].index(True)
        d = {}
        for i in range(len(self.graph.edges)):
            if i in ec:
                place = self.edgeclasses[[i in k for k in self.edgeclasses].index(True)].index(self.edgemap[i])
                mt = ecmap[[i in k for k in self.edgeclasses].index(True)]
                if mt >= 0:
                    d[i] = self.edgeclasses[mt][place]
                else:
                    d[i] = -1-self.edgeclasses[-1-mt][place]
            elif -1-i in ec:
                place = self.edgeclasses[[-1-i in k for k in self.edgeclasses].index(True)].index(self.edgemap[-1-i])
                mt = ecmap[[-1-i in k for k in self.edgeclasses].index(True)]
                if mt >= 0:
                    d[i] = -1-self.edgeclasses[mt][place]
                else:
                    d[i] = self.edgeclasses[-1-mt][place]
            else:
                newEdge = [self.vertmap[self.graph[i][0]],self.vertmap[self.graph[i][1]]]
                if newEdge in self.graph.edges:
                    d[i] = self.graph.edges.index(newEdge)
                else:
                    newEdge = [newEdge[1],newEdge[0]]
                    d[i] = -1-self.graph.edges.index(newEdge)
            d[-1-i] = -1-d[i]
                    
        return [self.vertmap, d]



def getIsom(graph1, graph2):
    if graph1.verts != graph2.verts:
        return None
    
    gs1 = GraphSymmetry(graph1)
    gs2 = GraphSymmetry(graph2)

    ret = {}

    for i in range(graph1.verts):
        if i not in sum(gs1.vertclasses, start=[]):
            for j in range(graph2.verts):
                if j not in sum(gs2.vertclasses, start=[]) and gs1.degs[i] == gs2.degs[j] and sorted(list(gs1.ndegs[i].values())) == sorted(list(gs2.ndegs[j].values())):
                    ret[i] = j
                    break
            else:
                return None

    vcpairs = {}
    #print(gs1.vertclasses)
    #print(gs2.vertclasses)
    for i in range(len(gs1.vertclasses)):
        for j in range(len(gs2.vertclasses)):
            if gs1.degs[gs1.vertclasses[i][0]] == gs2.degs[gs2.vertclasses[j][0]] and sorted(list(gs1.ndegs[gs1.vertclasses[i][0]].values())) == sorted(list(gs2.ndegs[gs2.vertclasses[j][0]].values())) and len(gs1.vertclasses[i]) == len(gs2.vertclasses[j]):
                vcpairs[i] = j
                break
        else:
            return None

    for i in range(len(gs1.vertclasses)):
        for j in range(len(gs1.vertclasses[i])):
            ret[gs1.vertclasses[i][j]] = gs2.vertclasses[vcpairs[i]][j]

    while True:
        if False not in [False not in [ret[j] in gs2.ndegs[ret[i]] and gs2.ndegs[ret[i]][ret[j]] == gs1.ndegs[i][j] for j in gs1.ndegs[i]] for i in range(graph1.verts)]:
            # calculate edges
            emap = {}
            for i in range(len(graph1.edges)):
                newEdge = [ret[graph1.edges[i][0]], ret[graph1.edges[i][1]]]
                for j in range(len(graph2.edges)):
                    if j in emap.values():
                        continue
                    if newEdge == graph2.edges[j]:
                        emap[i] = j
                        emap[-1-i] = -1-j
                        break
                    elif newEdge[0] == graph2.edges[j][1] and newEdge[1] == graph2.edges[j][0]:
                        emap[i] = -1-j
                        emap[-1-i] = j
                        break
                else:
                    raise ValueError

            return [ret, emap]
        
        for i in gs1.vertclasses:
            if incrementSeq(i, ret):
                break
        else:
            return None


#print('\n'.join([f"{i.vertmap}, {i.edgemap}" for i in GraphSymmetry(Graph(5,[[0,1],[0,2],[0,3],[0,4],[1,2],[1,2],[3,4],[3,4]]))]))
#print(getIsom(Graph(5,[[0,1],[0,2],[0,3],[0,4],[1,2],[1,2],[3,4],[3,4]]), Graph(5,[[1,0],[0,2],[0,2],[2,1],[1,3],[1,4],[3,4],[3,4]])))


def genRandGraph(v,e):
    return Graph(v,[[randint(0,v-1),randint(0,v-1)] for _ in range(e)])


def getCombinations(s):
    if not s:
        return [[]]
    else:
        c = getCombinations(s[1:])
        return c + [[s[0]] + i for i in c]


class Marking(Graph):
    def __init__(self, graph, base, loops, tree, labels):
        super().__init__(graph.verts, graph.edges)
        self.base = base
        self.loops = loops
        self.tree = tree
        self.labels = labels
        self.verifyLabels()

    def __eq__(self, other):
      try:
        if self.edges == [[0, 1], [2, 3], [2, 3], [0, 1], [0, 2], [1, 3]] and self.loops == [[0, -4], [4, 1, -6, -4], [4, 2, -6, -4]] and other.edges == [[0, 1], [3, 2], [3, 2], [0, 1], [1, 2], [0, 3]] and other.loops == [[0, -4], [5, 1, -5, -4], [5, 2, -5, -4]]:
            print('\n'.join([str(i.getMaps()) for i in GraphSymmetry(self)]))
          
        isom = getIsom(self, other)

        if isom is None:
            return False


        for i in GraphSymmetry(self):
            ii = i.getMaps()
            for j in range(len(self.loops)):
                if not Word([isom[1][i.getMaps()[1][k]] for k in self.loops[j]]).innEq(Word(other.loops[j])):
                    if self.edges == [[0, 1], [2, 3], [2, 3], [0, 1], [0, 2], [1, 3]] and self.loops == [[0, -4], [4, 1, -6, -4], [4, 2, -6, -4]] and other.edges == [[0, 1], [3, 2], [3, 2], [0, 1], [1, 2], [0, 3]] and other.loops == [[0, -4], [5, 1, -5, -4], [5, 2, -5, -4]]:
                        print([isom[1][i.getMaps()[1][k]] for k in self.loops[j]],other.loops[j])
                    break
            else:
                
            #    print(self.edges,self.loops)
             #   print(other.edges, other.loops)
              #  print(i.getMaps())
               # print("success")
                return True
        return False
      except KeyError:
          print("bruh")

    def verifyLabels(self):
        for i in range(len(self.loops)):
            ls = []
            for j in self.loops[i]:
                if j in self.labels:
                    for k in self.labels[j]:
                        ls.append(k)
                elif -1-j in self.labels:
                    for k in reversed(self.labels[-1-j]):
                        ls.append(-1-k)
            if not Word(ls).innEq(Word([i])):
                print(f"LABEL VERIF FAILED, LOOP {i}")
                print(f"Labels: {self.labels}")
                print(f"Loops: {self.loops}")
                # raise ValueError
                return False
        # print("LABEL VERIF SUCCESS")
        # print(f"Labels: {self.labels}")
        # print(f"Loops: {self.loops}")
        return True

    def generateTree(self, forest=None):
        if forest == None:
            newtree = []
            v = [self.base]
        else:
            newtree = forest
            v = [i for i in range(self.verts) if True in [i in self.edges[j] for j in forest]]

        ab = lambda n: n if n >= 0 else -1-n
        
        while len(v) < self.verts:
            for i in range(-len(self.edges), len(self.edges)):
                if ab(i) in newtree: continue
                if self[i][0] in v and self[i][1] not in v:
                    newtree.append(ab(i))
                    v.append(self[i][1])
        
        paths = self.getPaths(self.base, newtree)

        lab2 = {}
        for i in range(len(self.edges)):
            if i in newtree: continue
            lab2[i] = Word(sum([self.labels[k] if k in self.labels else ([-1-ii for ii in reversed(self.labels[-1-k])] if -1-k in self.labels else []) for k in paths[self.edges[i][0]] + [i] + [-1-j for j in reversed(paths[self.edges[i][1]])]],start=[])).ls

        return (newtree, lab2)

    def collapseEdge(self, e):
        x = sorted(self.edges[e])
        if e in self.tree:
            tr = self.tree
            lab = self.labels
        else:
            (tr, lab) = self.generateTree([e])
        
        return Marking(super().collapseEdge(e),
                       x[0] if self.base == x[1] else (self.base - 1 if self.base > x[1] else self.base),
                       [[j if abs(j) <= e else (j - 1 if j >= 0 else j + 1) for j in i if j != e and j != -1-e] for i in self.loops],
                       [j if j < e else j - 1 for j in tr if j != e],
                       {(i if i < e else i - 1): lab[i] for i in lab})


    def expandVertex(self, v, e): # v is the vertex to expand, e is the list of oriented edges ending at the new vertex
        loops = deepcopy(self.loops)

        for i in range(len(loops)):
            j = 1
            if self.base == v and -1-loops[i][0] in e:
                loops[i].insert(0, len(self.edges))
                j += 1
            while j < len(loops[i]):
                if self[loops[i][j-1]][1] == v and self[loops[i][j]][0] == v:
                    if loops[i][j-1] not in e and -1-loops[i][j] in e:
                        loops[i].insert(j, len(self.edges))
                        j += 1
                    elif loops[i][j-1] in e and -1-loops[i][j] not in e:
                        loops[i].insert(j, -1-len(self.edges))
                        j += 1
                j += 1
            if self.base == v and loops[i][-1] in e:
                loops[i].append(-1-len(self.edges))

        return Marking(super().expandVertex(v, e), self.base, loops, self.tree + [len(self.edges)], self.labels)

    def getCollapses(self):
        return [[self.collapseEdge(e), e] for e in range(len(self.edges)) if self.edges[e][0] != self.edges[e][1]]

    def getExpansions(self):
        return sum([[[self.expandVertex(i,j), [i, j]] for j in getCombinations(self.getEdgesTo(i)[1:]) if len(j) > 1 and len(j) < len(self.getEdgesTo(i)) - 1] for i in range(self.verts)], start=[])


def Rose(n):
    return Marking(Graph(1,[[0,0] for i in range(n)]), 0, [[i] for i in range(n)], [], {i:[i] for i in range(n)})


class Vec:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def __add__(self, other):
        return Vec(self.x + other.x, self.y + other.y)

    def __sub__(self, other):
        return Vec(self.x - other.x, self.y - other.y)
    
    def __mul__(self, sc):
        return Vec(self.x * sc, self.y * sc)

    def mag(self):
        return sqrt(self.x**2 + self.y**2)

    def norm(self):
        return self * ((1/self.mag()) if self.mag() != 0 else 1)

    def plot(self, canvas, color = "black"):
        return canvas.create_oval(self.x - 3, self.y - 3, self.x + 3, self.y + 3, fill=color)

    def dot(self, other):
        return self.x * other.x + self.y * other.y

    def transform(self, origin, scale):
        return self * scale + origin

    def rotate(self, angle):
        return Vec(cos(angle)*self.x - sin(angle)*self.y, sin(angle)*self.x + cos(angle)*self.y)


class Particle:
    def __init__(self, pos, vel):
        self.pos = pos
        self.vel = vel

    def sim(self):
        self.pos += self.vel
        self.vel *= 0.9
        return self.vel.mag()

    def changeVel(self, dv):
        self.vel += dv



def attract(ee, o, level, desire):
    ee.changeVel((ee.pos - o.pos).norm() * level * (desire - (ee.pos - o.pos).mag()))

def repel(ors, ees, level, desire, dont=False):
    for i in range(len(ees)):
        for j in range(len(ors)):
            if (ees[i].pos - ors[j].pos).mag() < desire or dont:
                attract(ees[i], ors[j], level, desire)

def attractGraph(ees, graph, level, desire):
    for i in graph.edges:
        attract(ees[i[0]], ees[i[1]], level, desire)
        attract(ees[i[1]], ees[i[0]], level, desire)

def sim(parts):
    return sum([i.sim() for i in parts])

def genRandPos(n):
    return [Particle(Vec(i + randint(-5,5),i + randint(-5,5)),Vec(0,0)) for i in range(n)]



class SimGraph:
    def __init__(self, graph, pos, scale):
        self.graph = graph
        self.vertexPos = genRandPos(graph.verts)
        self.edgePos = genRandPos(len(graph.edges))
        self.pos = pos
        self.scale = scale

    def simFrame(self, scale=False, noEdgePhysics=False):
        # simulate vertices
        repel([Particle(Vec(0,0),Vec(0,0))], self.vertexPos, 0.005, 0, dont=True) # gravity
        #if not noEdgePhysics:
        repel(self.vertexPos, self.vertexPos, 0.005, 250) # repulsion
        #else:
        #repel([self.vertexPos[0]], self.vertexPos, 0.005, 1000)
        attractGraph(self.vertexPos, self.graph, 0.1, 100) # edge attraction
        sim(self.vertexPos)

        if noEdgePhysics:
            for k in range(len(self.graph.edges)):
                [i, j] = self.graph.edges[k]
                self.edgePos[k].pos = (self.vertexPos[i].pos + self.vertexPos[j].pos) * 0.5

        else:


            # simualte edges
            repel(self.edgePos, self.edgePos, 0.2, 50) # repulsion

            # attract each edge centre to its vertices
            for k in range(len(self.graph.edges)):
                [i, j] = self.graph.edges[k]
                attract(self.edgePos[k], Particle((self.vertexPos[i].pos + self.vertexPos[j].pos) * 0.5, Vec(0, 0)), 0.1, 0 if i != j else 30)

            ret = sim(self.edgePos)
            
            # align the edge centre to the perpendicular
            for k in range(len(self.graph.edges)):
                [i, j] = self.graph.edges[k]
                if i != j: self.edgePos[k].pos -= (self.vertexPos[i].pos - self.vertexPos[j].pos).norm() * (self.edgePos[k].pos - (self.vertexPos[i].pos + self.vertexPos[j].pos) * 0.5).dot((self.vertexPos[i].pos - self.vertexPos[j].pos).norm())
                else:
                    self.edgePos[k].pos += (lambda v: v * ((40 - v.mag())/v.mag()))(self.edgePos[k].pos - self.vertexPos[i].pos)
                self.edgePos[k].vel *= 0.5

        if scale:
            xs = [i.pos.x for i in self.vertexPos + self.edgePos]
            ys = [i.pos.y for i in self.vertexPos + self.edgePos]
            
            self.scale = 75 / (max(max(xs) - min(xs), max(ys) - min(ys)) + 1)

        return 0

    def draw(self, canvas, colorEdges = None, colorVertices = None):
        centre = Vec(sum([i.pos.x for i in self.vertexPos + self.edgePos])/(len(self.vertexPos)+len(self.edgePos)),
                     sum([i.pos.y for i in self.vertexPos + self.edgePos])/(len(self.vertexPos)+len(self.edgePos)))
        
        self.pos -= centre
        
        if colorEdges is None:
            colorEdges = {}
        if colorVertices is None:
            colorVertices = {}
        objs = []
        for i in range(len(self.vertexPos)):
            objs.append(self.vertexPos[i].pos.transform(self.pos, self.scale).plot(C, "black" if i not in colorVertices else colorVertices[i]))

        for k in range(len(self.graph.edges)):
            [i, j] = self.graph.edges[k]
            if i == j:
                objs.append((lambda a1,a2,a3,a4,a5,col: C.create_line(a1.x,a1.y,a1.x,a1.y,a2.x,a2.y,a3.x,a3.y,a4.x,a4.y,a5.x,a5.y,a5.x,a5.y,smooth=True, fill=col))(
                    self.vertexPos[i].pos.transform(self.pos, self.scale),
                    ((self.vertexPos[i].pos - self.edgePos[k].pos).rotate(pi/4) * 0.5 + self.edgePos[k].pos).transform(self.pos, self.scale),
                    self.edgePos[k].pos.transform(self.pos, self.scale),
                    ((self.vertexPos[i].pos - self.edgePos[k].pos).rotate(-pi/4) * 0.5 + self.edgePos[k].pos).transform(self.pos, self.scale),
                    self.vertexPos[j].pos.transform(self.pos, self.scale),
                    "black" if k not in colorEdges else colorEdges[k]))
            else:
                objs.append((lambda a1,a2,a3,col,arr: C.create_line(a1.x,a1.y,a2.x,a2.y,a3.x,a3.y,smooth=True, fill=col,arrow=arr))(
                    self.vertexPos[i].pos.transform(self.pos, self.scale),
                    self.edgePos[k].pos.transform(self.pos, self.scale),
                    self.vertexPos[j].pos.transform(self.pos, self.scale),
                    "black" if k not in colorEdges else colorEdges[k], "last" if type(self.graph) == Marking and k in self.graph.labels else "none"))
            if type(self.graph) == Marking and k in self.graph.labels:
                objs.append(canvas.create_text(self.edgePos[k].pos.transform(self.pos, self.scale).x,
                                               self.edgePos[k].pos.transform(self.pos, self.scale).y,
                                               text="".join([chr(65+ii) if ii >= 0 else chr(96-ii) for ii in self.graph.labels[k]]),
                                               fill="black"))
            # objs.append(self.edgePos[k].pos.transform(self.pos, self.scale).plot(C))
            
        self.pos += centre
        
        return objs

    def locateObj(self, pos):
        e = [(pos - i.pos.transform(self.pos, self.scale)).mag() for i in self.edgePos]
        v = [(pos - i.pos.transform(self.pos, self.scale)).mag() for i in self.vertexPos]
        if min(e) < min(v): return [e.index(min(e)), "edge"] if min(e) < 40 else [-1, "failed"]
        else: return [v.index(min(v)), "vert"] if min(v) < 40 else [-1, "failed"]

    def collapseEdge(self, edge):
        del self.edgePos[edge]
        del self.vertexPos[max(self.graph.edges[edge])]
        self.graph = self.graph.collapseEdge(edge)

    def expandVertex(self, vertex, edges):
        self.graph = self.graph.expandVertex(vertex, edges)
        self.edgePos.append(Particle(Vec(randint(-5,5),randint(-5,5)),Vec(0,0)))
        self.vertexPos.append(Particle(Vec(randint(-5,5),randint(-5,5)),Vec(0,0)))


class IdleState:
    pass

class ReloadState:
    pass

class EdgeSelectedState:
    def __init__(self, selected):
        self.selected = selected

class VertexSelectedState:
    def __init__(self, vertex):
        self.vertex = vertex
        self.edges = []


def makeIdealEdge(marking, edge):
    vset = [marking.edges[edge][1]]
    vnset = [marking.edges[edge][0]]
    seenList = [edge]
    while seenList != marking.tree:
        for i in marking.tree:
            if i in seenList:
                continue
            if marking.edges[i][0] in vset:
                vset.append(marking.edges[i][1])
                seenList.append(i)
                break
            elif marking.edges[i][1] in vset:
                vset.append(marking.edges[i][0])
                seenList.append(i)
                break
            elif marking.edges[i][0] in vnset:
                vnset.append(marking.edges[i][1])
                seenList.append(i)
                break
            elif marking.edges[i][1] in vnset:
                vnset.append(marking.edges[i][0])
                seenList.append(i)
                break
        else:
            print('Error!', marking.edges,edge,marking.tree,seenList)
        seenList = sorted(seenList)
    return [vset,vnset]


class StarViewState:
    def __init__(self, graph, expMode):
        global sgraph
        self.expMode = expMode
        self.graph = graph

        if expMode:
            st = []
            diredges = []
            for i in range(len(graph.edges)):
                if i not in graph.tree:
                    diredges.append(i)
            
            for i in graph.tree:
                [vset,vnset] = makeIdealEdge(graph, i)
                if graph.edges[diredges[0]][0] in vnset:
                    vset = vnset
                iedge = 0
                for j in range(len(diredges)):
                    if graph.edges[diredges[j]][0] in vset:
                        iedge |= (1 << (2*j))
                    if graph.edges[diredges[j]][1] in vset:
                        iedge |= (1 << (2*j+1))
                st.append(iedge)

            st = sorted(st)
            print('st:',st)
            
            self.layers = generateStar(len(self.graph.edges) - self.graph.verts + 1, start=None if st == [] else [st])
            if False and st == []:
                self.layers = [[[]]] + self.layers
            print(self.layers)
            layerIndex = [len(sum(self.layers[:i],start=[])) for i in range(len(self.layers))]
            self.star = Graph(len(sum(self.layers,start=[])), [[layerIndex[i-1] + j, layerIndex[i] + k] for i in range(1,len(self.layers)) for j in range(len(self.layers[i-1])) for k in range(len(self.layers[i])) if False not in [l in self.layers[i][k] for l in self.layers[i-1][j]]])
            sgraph = SimGraph(self.star, Vec(500,300),0.5)

            return
        
        self.layers = [[[graph, []]]]
        while True:
            newLayer = []
            for i in range(len(self.layers[-1])):
                newLayer += [[j[0],i] for j in (lambda x: x.getExpansions() if expMode else x.getCollapses())(self.layers[-1][i][0])]
            if not newLayer:
                break
            newLayer = getEquivalenceClasses(newLayer, lambda a, b: a[0] == b[0])
            newLayer = [[i[0][0], [j[1] for j in i]] for i in newLayer]
            self.layers.append(newLayer)
            print("\n\nLayer Done\n\n")

        layerIndex = [len(sum(self.layers[:i],start=[])) for i in range(len(self.layers))]
        self.star = Graph(len(sum(self.layers,start=[])), [[layerIndex[i-1] + self.layers[i][j][1][k], layerIndex[i] + j] for i in range(len(self.layers)) for j in range(len(self.layers[i])) for k in range(len(self.layers[i][j][1]))])
        sgraph = SimGraph(self.star, Vec(500,300),0.5)
        print(self.star.verts, "verts")
        # print(self.star.edges, "edges")

    def end(self):
        global sgraph
        sgraph = SimGraph(self.graph, Vec(500,300), 2)


root = Tk()

C = Canvas(root, bg="white", height=600, width=1000)

C.pack()

sgraph = SimGraph(Rose(4), Vec(500,300),2) # Graph(6, [[0,1],[0,2],[0,3],[1,4],[1,4],[2,4],[2,5],[3,5],[3,5]]), Vec(500,300), 1)

collgraphs = []
expgraphs = []
cgwindow = 0

def updateCollGraphs():
    global collgraphs, expgraphs, cgwindow
    cgwindow = 0
    g = sgraph.graph.getCollapses()
    collgraphs = [[SimGraph(g[i][0], Vec(50 + 100*i, 550), 0.5), g[i][1]] for i in range(len(g))]
    g = sgraph.graph.getExpansions()
    expgraphs = [[SimGraph(g[i][0], Vec(50 + 100*i, 50), 0.5), g[i][1]] for i in range(len(g))]

updateCollGraphs()

state = IdleState()


def onP(g):
    print(sgraph.graph.verts, sgraph.graph.edges, sgraph.graph.loops)


def onLeft(g):
    global cgwindow
    if cgwindow == 0:
        return
    cgwindow -= 1
    for i in collgraphs:
        i[0].pos.x += 100
    for i in expgraphs:
        i[0].pos.x += 100

def onRight(g):
    global cgwindow
    cgwindow += 1
    for i in collgraphs:
        i[0].pos.x -= 100
    for i in expgraphs:
        i[0].pos.x -= 100

def onS(g):
    global state
    if type(state) == StarViewState:
        if state.expMode:
            state.end()
            state = IdleState()
        else:
            state.end()
            state = StarViewState(state.graph, True)
    else:
        state = StarViewState(sgraph.graph, False)

def onR(g):
    global state
    state = ReloadState()

def onL(g):
    while True:
        for i in range(-len(sgraph.graph.labels),len(sgraph.graph.labels)):
            newlabs = {j: Word([i] + sgraph.graph.labels[j] + [-1-i]).ls for j in sgraph.graph.labels}
            if len(sum(newlabs.values(), start = [])) < len(sum(sgraph.graph.labels.values(), start = [])):
                sgraph.graph.labels = newlabs
                break
        else:
            break

def onEnter(g):
    global state
    if type(state) == VertexSelectedState:
        sgraph.expandVertex(state.vertex, state.edges) # [i if sgraph.graph[i][1] == state.vertex else -1-i for i in state.edges] + [-1-i for i in state.edges if sgraph.graph[i][0] == sgraph.graph[i][1]] + state.floops + [-1-i for i in state.bloops])
        state = IdleState()
        updateCollGraphs()
        print(sgraph.graph.tree)

def onClick(event):
    global state

    if event.y < 100:
        sel = event.x // 100 + cgwindow
        if sel < len(expgraphs):
            if type(state) != VertexSelectedState or state.vertex != expgraphs[sel][1][0] or (state.edges != expgraphs[sel][1][1] and False in [(j in state.edges) != (j in expgraphs[sel][1][1]) for j in sgraph.graph.getEdgesTo(state.vertex)]):
                state = VertexSelectedState(expgraphs[sel][1][0])
                state.edges = expgraphs[sel][1][1]
            else:
                onEnter(None)
            return

    elif event.y > 500:
        sel = event.x // 100 + cgwindow
        if sel < len(collgraphs):
            if type(state) != EdgeSelectedState or state.selected != collgraphs[sel][1]:
                print("clicked: ", sel)
                state = EdgeSelectedState(collgraphs[sel][1])
            else:
                sgraph.collapseEdge(state.selected) # collapse the edge
                updateCollGraphs()
                state = IdleState()
            return
    
    ns = sgraph.locateObj(Vec(event.x, event.y))

    if type(state) == IdleState:
        if ns[1] == "edge" and sgraph.graph.edges[ns[0]][0] != sgraph.graph.edges[ns[0]][1]:
            state = EdgeSelectedState(ns[0]) # select an edge for collapse
        elif ns[1] == "vert":
            state = VertexSelectedState(ns[0]) # select a vertex for blow-up
    elif type(state) == EdgeSelectedState:
        if ns[1] == "edge" and ns[0] == state.selected:
            sgraph.collapseEdge(state.selected) # collapse the edge
            updateCollGraphs()
        state = IdleState()
    elif type(state) == VertexSelectedState:
        if ns[1] == "edge":
            if state.vertex in sgraph.graph.edges[ns[0]]:
                if sgraph.graph.edges[ns[0]][1] != state.vertex:
                    ns[0] = -1-ns[0]
                elif sgraph.graph.edges[ns[0]][0] == state.vertex: # loop
                    if ns[0] in state.edges:
                        if -1-ns[0] in state.edges: # blue
                            state.edges.remove(-1-ns[0])
                        else: # green
                            state.edges.remove(ns[0])
                            state.edges.append(-1-ns[0])
                    else:
                        if -1-ns[0] in state.edges: # yellow
                            state.edges.remove(-1-ns[0])
                        else: # black
                            state.edges.append(ns[0])
                            state.edges.append(-1-ns[0])
                    state.edges = sorted(state.edges)
                    return

                if ns[0] in state.edges:
                    state.edges.remove(ns[0]) # de-select edge
                else:
                    state.edges.append(ns[0]) # select edge

                state.edges = sorted(state.edges)
        else:
            state = IdleState()

root.bind("<Left>", onLeft)
root.bind("<Right>", onRight)
root.bind("r", onR)
root.bind("l", onL)
root.bind("s", onS)
root.bind("p", onP)
root.bind("<Return>", onEnter)
root.bind("<1>", onClick)

GRAPH_RANK = 2

while True:
    #for _ in range(int(sgraph.simFrame() / 10)):

    sgraph.simFrame(False, type(state) == StarViewState)

    for i in collgraphs[cgwindow:cgwindow+10]:
        i[0].simFrame(True)

    for i in expgraphs[cgwindow:cgwindow+10]:
        i[0].simFrame(True)

    objs = []
    if type(state) == IdleState:
        objs = sgraph.draw(C)
    elif type(state) == EdgeSelectedState:
        objs = sgraph.draw(C, {state.selected:"blue"})
    elif type(state) == VertexSelectedState:
        objs = sgraph.draw(C, {i:("black" if i not in state.edges and -1-i not in state.edges else ("blue" if sgraph.graph[i][0] != sgraph.graph[i][1] or (i in state.edges and -1-i in state.edges) else ("green" if i in state.edges else "yellow"))) for i in range(len(sgraph.graph.edges))}, {state.vertex:"red"})
    elif type(state) == StarViewState:
        objs = sgraph.draw(C, None, {0:"red"})

    objs += sum([i[0].draw(C, {} if type(state) != EdgeSelectedState or state.selected != i[1] else {j:"blue" for j in range(len(i[0].graph.edges))}) for i in collgraphs[cgwindow:cgwindow+10]],start=[])
    objs += sum([i[0].draw(C, {} if type(state) != VertexSelectedState or state.vertex != i[1][0] or (state.edges != i[1][1] and False in [(j in state.edges) != (j in i[1][1]) for j in sgraph.graph.getEdgesTo(state.vertex)]) else {j:"blue" for j in range(len(i[0].graph.edges))}) for i in expgraphs[cgwindow:cgwindow+10]],start=[])

    root.update()

    for i in objs:
        C.delete(i)

    if type(state) == ReloadState:
        sgraph = SimGraph(Rose(GRAPH_RANK), Vec(500,300),2)
        GRAPH_RANK += 1
        updateCollGraphs()
        state = IdleState()
