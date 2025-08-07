from z3 import *
import json

def main():
    A = Int('A')
    B = Int('B')
    C = Int('C')
    
    s = Solver()
    
    cities = ["Paris", "Porto", "Reykjavik"]
    lengths = [6, 7, 2]
    
    s.add(A >= 0, A <= 2)
    s.add(B >= 0, B <= 2)
    s.add(C >= 0, C <= 2)
    s.add(Distinct(A, B, C))
    
    lenA = If(A == 0, lengths[0], If(A == 1, lengths[1], lengths[2]))
    lenB = If(B == 0, lengths[0], If(B == 1, lengths[1], lengths[2]))
    lenC = If(C == 0, lengths[0], If(C == 1, lengths[1], lengths[2]))
    
    s.add(lenA + lenB + lenC == 15)
    
    s.add(Or(A == 0, A == 1))
    s.add(Or(C == 0, C == 2))
    
    s.add(Not(And(A == 1, B == 2)))
    s.add(Not(And(A == 2, B == 1)))
    s.add(Not(And(B == 1, C == 2)))
    s.add(Not(And(B == 2, C == 1)))
    
    if s.check() == sat:
        m = s.model()
        a_val = m[A].as_long()
        b_val = m[B].as_long()
        c_val = m[C].as_long()
        
        lenA_val = lengths[a_val]
        lenB_val = lengths[b_val]
        lenC_val = lengths[c_val]
        
        end0 = 7
        end1 = 7 + lenA_val - 1
        end2 = end1 + lenB_val - 1
        
        itinerary = [
            {"start": 1, "end": 7, "city": "Geneva"},
            {"start": 7, "end": end1, "city": cities[a_val]},
            {"start": end1, "end": end2, "city": cities[b_val]},
            {"start": end2, "end": 19, "city": cities[c_val]},
            {"start": 19, "end": 23, "city": "Oslo"}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()