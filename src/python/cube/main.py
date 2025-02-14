


# rotations are counter clockwise.

class Cube():
    def __init__(self):
        self.sides = "LRUDFB"

    def L(self): return self.sides[0]
    def R(self): return self.sides[1]
    def U(self): return self.sides[2]
    def D(self): return self.sides[3]
    def F(self): return self.sides[4]
    def B(self): return self.sides[5]
    
    def rotx(self):
        '''
        LRUDFB
        LRBFUD        
        '''
        c = Cube()
        c.sides = self.L() + self.R() + self.B() + self.F() + self.U() + self.D()
        return c
        
    def rotz(self):
        '''
        LRUDFB
        BFUDLR
        '''
        c = Cube()
        c.sides = self.B() + self.F() + self.U() + self.D() + self.L() + self.R() 
        return c

    def roty(self):
        '''
        LRUDFB
        UDRLFB
        '''
        c = Cube()
        c.sides = self.U() + self.D() + self.R() + self.L() + self.F() + self.B()
        return c
        
    def __eq__(self, o):
        return o.sides == self.sides

    def __hash__(self):
        return hash(self.sides)
    
    def __repr__(self): return self.sides

def explore(c, seen):
    if c in seen: return
    seen.add(c)
    print(f'{c} -> {c.rotx()} [label="rx"];')
    explore(c.rotx(), seen)
    print(f'{c} -> {c.roty()} [label="ry"];')
    explore(c.roty(), seen)
    print(f'{c} -> {c.rotz()} [label="rz"];')
    explore(c.rotz(), seen)
    
    
def main():
    C = Cube()
    seen = set()
    print("digraph G {")
    print("nodesep=1.0;")
    print("ranksep=1.0;")
    print("layout=neato;")
    print("overlap=false;")
    explore(C, seen)
    print("}")
main()
    
