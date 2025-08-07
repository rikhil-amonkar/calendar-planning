from z3 import *

def main():
    s = Solver()
    num_days = 12
    # Create day variables: 0 = Dublin, 1 = Riga, 2 = Vilnius
    day_assignments = [Int(f'day_{i}') for i in range(num_days)]
    
    # Constraint: Day 1 must be Dublin (0)
    s.add(day_assignments[0] == 0)
    # Constraint: Day 12 must be Vilnius (2)
    s.add(day_assignments[-1] == 2)
    
    # Constraint: Minimum 2 days in Riga (1)
    s.add(Sum([If(day_assignments[i] == 1, 1, 0) for i in range(num_days)]) >= 2)
    
    # Constraint: Valid city transitions (Dublin→Riga→Vilnius)
    for i in range(num_days - 1):
        # Allow staying in same city or moving to next city
        s.add(day_assignments[i+1] >= day_assignments[i])
        s.add(day_assignments[i+1] <= day_assignments[i] + 1)
        # Prevent skipping directly from Dublin to Vilnius
        s.add(Not(And(day_assignments[i] == 0, day_assignments[i+1] == 2)))
    
    if s.check() == sat:
        model = s.model()
        assignments = [model.evaluate(day_assignments[i]).as_long() for i in range(num_days)]
        
        # Convert to itinerary segments
        itinerary = []
        current_city = assignments[0]
        start_day = 1
        
        for day_idx in range(1, num_days):
            if assignments[day_idx] != current_city:
                end_day = day_idx
                day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                itinerary.append({
                    'day_range': day_range,
                    'place': ['Dublin', 'Riga', 'Vilnius'][current_city]
                })
                current_city = assignments[day_idx]
                start_day = day_idx + 1
        
        # Add final segment
        day_range = f"Day {start_day}-{num_days}" if start_day != num_days else f"Day {num_days}"
        itinerary.append({
            'day_range': day_range,
            'place': ['Dublin', 'Riga', 'Vilnius'][current_city]
        })
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()