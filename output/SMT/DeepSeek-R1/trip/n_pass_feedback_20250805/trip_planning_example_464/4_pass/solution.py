from z3 import *

def main():
    d0, d1, d2, d3, d4 = Ints('d0 d1 d2 d3 d4')
    solver = Solver()
    
    # Duration constraints for each city
    solver.add(d0 >= 3, d0 <= 5)      # Krakow: min 3, max 5
    solver.add(d1 >= 2, d1 <= 4)      # Frankfurt: min 2, max 4
    solver.add(d2 >= 3, d2 <= 5)      # Dubrovnik: min 3, max 5
    solver.add(d3 >= 3, d3 <= 5)      # Naples: min 3, max 5
    solver.add(d4 >= 2, d4 <= 3)      # Oslo: min 2, max 3
    
    # Total city days must be 14 (18 total days - 4 travel days)
    solver.add(d0 + d1 + d2 + d3 + d4 == 14)
    
    # Calculate start/end days for cities and travel days
    s0 = 1
    e0 = s0 + d0 - 1
    s_t1 = e0 + 1
    e_t1 = s_t1  # travel days are 1 day
    s1 = e_t1 + 1
    e1 = s1 + d1 - 1
    s_t2 = e1 + 1
    e_t2 = s_t2
    s2 = e_t2 + 1
    e2 = s2 + d2 - 1
    s_t3 = e2 + 1
    e_t3 = s_t3
    s3 = e_t3 + 1
    e3 = s3 + d3 - 1
    s_t4 = e3 + 1
    e_t4 = s_t4
    s4 = e_t4 + 1
    e4 = s4 + d4 - 1
    
    # Ensure trip ends on day 18
    solver.add(e4 == 18)
    
    # Event constraints
    solver.add(s0 <= 1, e0 >= 3)    # Krakow covers days 1-3
    solver.add(s2 <= 5, e2 >= 9)    # Dubrovnik covers days 5-9
    solver.add(s4 <= 16, e4 >= 18)  # Oslo covers days 16-18
    
    if solver.check() == sat:
        model = solver.model()
        d0_val = model[d0].as_long()
        d1_val = model[d1].as_long()
        d2_val = model[d2].as_long()
        d3_val = model[d3].as_long()
        d4_val = model[d4].as_long()
        
        # Recalculate timeline using solved durations
        s0 = 1
        e0 = s0 + d0_val - 1
        s_t1 = e0 + 1
        s1 = s_t1 + 1
        e1 = s1 + d1_val - 1
        s_t2 = e1 + 1
        s2 = s_t2 + 1
        e2 = s2 + d2_val - 1
        s_t3 = e2 + 1
        s3 = s_t3 + 1
        e3 = s3 + d3_val - 1
        s_t4 = e3 + 1
        s4 = s_t4 + 1
        e4 = s4 + d4_val - 1
        
        # Build itinerary with travel days
        itinerary = [
            {'day_range': f'Day {s0}-{e0}', 'place': 'Krakow'},
            {'day_range': f'Day {s_t1}', 'place': 'Travel'},
            {'day_range': f'Day {s1}-{e1}', 'place': 'Frankfurt'},
            {'day_range': f'Day {s_t2}', 'place': 'Travel'},
            {'day_range': f'Day {s2}-{e2}', 'place': 'Dubrovnik'},
            {'day_range': f'Day {s_t3}', 'place': 'Travel'},
            {'day_range': f'Day {s3}-{e3}', 'place': 'Naples'},
            {'day_range': f'Day {s_t4}', 'place': 'Travel'},
            {'day_range': f'Day {s4}-{e4}', 'place': 'Oslo'}
        ]
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()