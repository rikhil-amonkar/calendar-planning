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
    
    # Calculate start and end days for each city
    s0 = 1
    e0 = s0 + d0 - 1
    s1 = e0 + 2  # +1 for travel day, +1 for next city start
    e1 = s1 + d1 - 1
    s2 = e1 + 2
    e2 = s2 + d2 - 1
    s3 = e2 + 2
    e3 = s3 + d3 - 1
    s4 = e3 + 2
    e4 = s4 + d4 - 1
    
    # Ensure the last day is day 18
    solver.add(e4 == 18)
    
    # Event constraints
    # Krakow must cover days 1-3
    solver.add(s0 <= 1, e0 >= 3)
    # Dubrovnik must cover days 5-9
    solver.add(s2 <= 5, e2 >= 9)
    # Oslo must cover days 16-18
    solver.add(s4 <= 16, e4 >= 18)
    
    if solver.check() == sat:
        model = solver.model()
        d0_val = model[d0].as_long()
        d1_val = model[d1].as_long()
        d2_val = model[d2].as_long()
        d3_val = model[d3].as_long()
        d4_val = model[d4].as_long()
        
        # Recalculate start and end days based on the model
        s0 = 1
        e0 = s0 + d0_val - 1
        s1 = e0 + 2
        e1 = s1 + d1_val - 1
        s2 = e1 + 2
        e2 = s2 + d2_val - 1
        s3 = e2 + 2
        e3 = s3 + d3_val - 1
        s4 = e3 + 2
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