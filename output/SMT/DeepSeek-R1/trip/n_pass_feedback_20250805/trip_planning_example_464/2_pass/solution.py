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
    
    # Total stay days must be 14 (since 18 total days - 4 travel days)
    solver.add(d0 + d1 + d2 + d3 + d4 == 14)
    
    # Constraint for Dubrovnik: d0 + d1 <= 6 (ensures Dubrovnik start day <= 9)
    solver.add(d0 + d1 <= 6)
    
    if solver.check() == sat:
        model = solver.model()
        d0_val = model[d0].as_long()
        d1_val = model[d1].as_long()
        d2_val = model[d2].as_long()
        d3_val = model[d3].as_long()
        d4_val = model[d4].as_long()
        
        # Calculate start and end days for each city
        s0 = 1
        e0 = s0 + d0_val - 1
        
        s1 = s0 + d0_val + 1
        e1 = s1 + d1_val - 1
        
        s2 = s1 + d1_val + 1
        e2 = s2 + d2_val - 1
        
        s3 = s2 + d2_val + 1
        e3 = s3 + d3_val - 1
        
        s4 = s3 + d3_val + 1
        e4 = s4 + d4_val - 1
        
        itinerary = [
            {'day_range': f'Day {s0}-{e0}', 'place': 'Krakow'},
            {'day_range': f'Day {s1}-{e1}', 'place': 'Frankfurt'},
            {'day_range': f'Day {s2}-{e2}', 'place': 'Dubrovnik'},
            {'day_range': f'Day {s3}-{e3}', 'place': 'Naples'},
            {'day_range': f'Day {s4}-{e4}', 'place': 'Oslo'}
        ]
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()