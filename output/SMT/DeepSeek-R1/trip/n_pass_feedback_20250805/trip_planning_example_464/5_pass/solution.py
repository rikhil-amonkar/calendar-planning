from z3 import *

def main():
    d0, d1, d2, d3, d4 = Ints('d0 d1 d2 d3 d4')
    s0, s1, s2, s3, s4 = Ints('s0 s1 s2 s3 s4')
    e0, e1, e2, e3, e4 = Ints('e0 e1 e2 e3 e4')
    t1, t2, t3, t4 = Ints('t1 t2 t3 t4')  # Travel days
    
    solver = Solver()
    
    # City duration constraints
    solver.add(d0 >= 3, d0 <= 5)  # Krakow
    solver.add(d1 >= 2, d1 <= 4)  # Frankfurt
    solver.add(d2 >= 3, d2 <= 5)  # Dubrovnik
    solver.add(d3 >= 3, d3 <= 5)  # Naples
    solver.add(d4 >= 2, d4 <= 3)  # Oslo
    
    # Start and end days
    solver.add(s0 == 1)  # Trip starts on day 1
    solver.add(e0 == s0 + d0 - 1)
    
    # Travel after Krakow
    solver.add(t1 == e0 + 1)
    solver.add(s1 == t1 + 1)
    solver.add(e1 == s1 + d1 - 1)
    
    # Travel after Frankfurt
    solver.add(t2 == e1 + 1)
    solver.add(s2 == t2 + 1)
    solver.add(e2 == s2 + d2 - 1)
    
    # Travel after Dubrovnik
    solver.add(t3 == e2 + 1)
    solver.add(s3 == t3 + 1)
    solver.add(e3 == s3 + d3 - 1)
    
    # Travel after Naples
    solver.add(t4 == e3 + 1)
    solver.add(s4 == t4 + 1)
    solver.add(e4 == s4 + d4 - 1)
    
    # Total days constraint (18 days with 4 travel days)
    solver.add(e4 == 18)
    solver.add(d0 + d1 + d2 + d3 + d4 == 14)  # 18 total days - 4 travel days
    
    # Event constraints
    # Krakow covers days 1,2,3
    solver.add(s0 <= 1, e0 >= 3)
    
    # Dubrovnik covers days 5-9
    solver.add(s2 <= 5, e2 >= 9)
    
    # Oslo covers days 16-18
    solver.add(s4 <= 16, e4 >= 18)
    
    if solver.check() == sat:
        model = solver.model()
        d0_val = model[d0].as_long()
        d1_val = model[d1].as_long()
        d2_val = model[d2].as_long()
        d3_val = model[d3].as_long()
        d4_val = model[d4].as_long()
        
        # Rebuild timeline
        s0_val = 1
        e0_val = s0_val + d0_val - 1
        t1_val = e0_val + 1
        s1_val = t1_val + 1
        e1_val = s1_val + d1_val - 1
        t2_val = e1_val + 1
        s2_val = t2_val + 1
        e2_val = s2_val + d2_val - 1
        t3_val = e2_val + 1
        s3_val = t3_val + 1
        e3_val = s3_val + d3_val - 1
        t4_val = e3_val + 1
        s4_val = t4_val + 1
        e4_val = s4_val + d4_val - 1
        
        itinerary = [
            {"day_range": f"Day {s0_val}-{e0_val}", "place": "Krakow"},
            {"day_range": f"Day {t1_val}", "place": "Travel"},
            {"day_range": f"Day {s1_val}-{e1_val}", "place": "Frankfurt"},
            {"day_range": f"Day {t2_val}", "place": "Travel"},
            {"day_range": f"Day {s2_val}-{e2_val}", "place": "Dubrovnik"},
            {"day_range": f"Day {t3_val}", "place": "Travel"},
            {"day_range": f"Day {s3_val}-{e3_val}", "place": "Naples"},
            {"day_range": f"Day {t4_val}", "place": "Travel"},
            {"day_range": f"Day {s4_val}-{e4_val}", "place": "Oslo"}
        ]
        
        plan = {"itinerary": itinerary}
        print(f"Found valid plan:\n{plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()