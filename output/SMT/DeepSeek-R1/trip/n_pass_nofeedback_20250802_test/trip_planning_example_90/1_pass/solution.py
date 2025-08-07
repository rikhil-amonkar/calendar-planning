import z3
import json

def main():
    s0, e0, s1, e1, s2, e2 = z3.Ints('s0 e0 s1 e1 s2 e2')
    solver = z3.Solver()
    
    # Segment 0: Naples (5 days including days 1-5)
    solver.add(s0 == 1)
    solver.add(e0 == s0 + 4)  # 5 days: s0 to s0+4 (inclusive)
    
    # Segment 1: Vienna (7 days starting at the end of Naples)
    solver.add(s1 == e0)
    solver.add(e1 == s1 + 6)  # 7 days: s1 to s1+6 (inclusive)
    
    # Segment 2: Vilnius (7 days starting at the end of Vienna)
    solver.add(s2 == e1)
    solver.add(e2 == s2 + 6)  # 7 days: s2 to s2+6 (inclusive)
    
    # Total trip must end on day 17
    solver.add(e2 == 17)
    
    if solver.check() == z3.sat:
        m = solver.model()
        s0_val = m[s0].as_long()
        e0_val = m[e0].as_long()
        s1_val = m[s1].as_long()
        e1_val = m[e1].as_long()
        s2_val = m[s2].as_long()
        e2_val = m[e2].as_long()
        
        itinerary = [
            {"from": s0_val, "to": e0_val, "city": "Naples"},
            {"from": s1_val, "to": e1_val, "city": "Vienna"},
            {"from": s2_val, "to": e2_val, "city": "Vilnius"}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()