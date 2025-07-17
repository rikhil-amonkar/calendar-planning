from z3 import *

def main():
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    d = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }
    
    direct_flights_tuples = [
        ('Hamburg', 'Frankfurt'),
        ('Naples', 'Mykonos'),
        ('Hamburg', 'Porto'),
        ('Hamburg', 'Geneva'),
        ('Mykonos', 'Geneva'),
        ('Frankfurt', 'Geneva'),
        ('Frankfurt', 'Porto'),
        ('Geneva', 'Porto'),
        ('Geneva', 'Manchester'),
        ('Naples', 'Manchester'),
        ('Frankfurt', 'Naples'),
        ('Frankfurt', 'Manchester'),
        ('Naples', 'Geneva'),
        ('Porto', 'Manchester'),
        ('Hamburg', 'Manchester')
    ]
    
    # Create Z3 variables
    pos = {c: Int(f'pos_{c}') for c in cities}
    s_day = {c: Int(f's_{c}') for c in cities}
    
    solver = Solver()
    
    # Each city has a distinct position between 0 and 6
    solver.add(Distinct([pos[c] for c in cities]))
    for c in cities:
        solver.add(pos[c] >= 0, pos[c] <= 6)
    
    # Define start day for each city
    for c in cities:
        sum_before = 0
        for other in cities:
            if other == c:
                continue
            sum_before += If(pos[other] < pos[c], d[other], 0)
        solver.add(s_day[c] == 1 + sum_before - pos[c])
    
    # Fixed constraints for Frankfurt
    solver.add(s_day['Frankfurt'] == 5)
    
    # Constraints for Mykonos and Manchester
    solver.add(s_day['Mykonos'] >= 8, s_day['Mykonos'] <= 12)
    solver.add(s_day['Manchester'] >= 12, s_day['Manchester'] <= 15)
    
    # Direct flight constraints for consecutive cities
    for c1 in cities:
        for c2 in cities:
            if c1 == c2:
                continue
            is_consecutive = (pos[c2] == pos[c1] + 1)
            allowed = False
            for (a, b) in direct_flights_tuples:
                allowed = Or(allowed, Or(And(c1 == a, c2 == b), And(c1 == b, c2 == a)))
            solver.add(Implies(is_consecutive, allowed))
    
    # Bounds for start days and end days
    for c in cities:
        solver.add(s_day[c] >= 1)
        solver.add(s_day[c] + d[c] - 1 <= 18)
    
    # Solve the problem
    if solver.check() == sat:
        m = solver.model()
        # Get the order of cities
        city_order = sorted(cities, key=lambda c: m.eval(pos[c]).as_long())
        itinerary = []
        
        for idx, c in enumerate(city_order):
            start = m.eval(s_day[c]).as_long()
            duration = d[c]
            end = start + duration - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": c})
            
            if idx < len(city_order) - 1:
                next_c = city_order[idx + 1]
                itinerary.append({"day_range": f"Day {end}", "place": c})
                itinerary.append({"day_range": f"Day {end}", "place": next_c})
        
        # Output the itinerary in JSON format
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()