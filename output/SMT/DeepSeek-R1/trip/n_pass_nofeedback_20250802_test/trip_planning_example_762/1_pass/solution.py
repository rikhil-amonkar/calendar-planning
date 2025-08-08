from z3 import *
import json

def main():
    # Define cities and their required days
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    required_days = {
        'Dublin': 3,
        'Madrid': 2,
        'Oslo': 3,
        'London': 2,
        'Vilnius': 3,
        'Berlin': 5
    }
    
    # Event constraints: (city, [days])
    events = {
        'Dublin': [7, 8, 9],
        'Madrid': [2, 3],
        'Berlin': [3, 4, 5, 6, 7]
    }
    
    # Direct flights list (as strings)
    flight_list_str = [
        "London and Madrid",
        "Oslo and Vilnius",
        "Berlin and Vilnius",
        "Madrid and Oslo",
        "Madrid and Dublin",
        "London and Oslo",
        "Madrid and Berlin",
        "Berlin and Oslo",
        "Dublin and Oslo",
        "London and Dublin",
        "London and Berlin",
        "Berlin and Dublin"
    ]
    
    # Create set of flight pairs (canonical order: (min, max))
    flight_pairs = set()
    for s in flight_list_str:
        a, b = s.split(' and ')
        flight_pairs.add((min(a, b), max(a, b)))
    
    # Days 1 to 13
    days = list(range(1, 14))
    
    # Create Z3 variables: x[day][city] = Bool(f'x_{day}_{city}')
    x = {}
    for d in days:
        x[d] = {}
        for c in cities:
            x[d][c] = Bool(f"x_{d}_{c}")
    
    s = Solver()
    
    # Constraint 1: Each day, at least one city and at most two cities
    for d in days:
        # At least one city
        s.add(Or([x[d][c] for c in cities]))
        # At most two cities: for any three distinct cities, not all true
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1 = cities[i]
                    c2 = cities[j]
                    c3 = cities[k]
                    s.add(Not(And(x[d][c1], x[d][c2], x[d][c3])))
    
    # Constraint 2: Total days per city
    for c in cities:
        total = Sum([If(x[d][c], 1, 0) for d in days])
        s.add(total == required_days[c])
    
    # Constraint 3: If two cities on same day, they must be connected by direct flight
    for d in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                pair = (min(c1, c2), max(c1, c2))
                # If both true, then pair must be in flight_pairs
                s.add(Implies(And(x[d][c1], x[d][c2]), pair in flight_pairs))
    
    # Constraint 4: Travel constraints (leaving and arriving)
    for c in cities:
        for d in range(1, 13):  # d from 1 to 12
            # If leaving c: in c on day d and not on day d+1
            cond1 = And(x[d][c], Not(x[d+1][c]))
            # Then there exists another city c2 connected to c and present on day d
            options1 = []
            for c2 in cities:
                if c2 != c:
                    pair = (min(c, c2), max(c, c2))
                    if pair in flight_pairs:
                        options1.append(And(x[d][c2]))
            if options1:
                s.add(Implies(cond1, Or(options1)))
            else:
                # If no options, then condition cannot hold
                s.add(Not(cond1))
                
            # If arriving in c: not in c on day d and in c on day d+1
            cond2 = And(Not(x[d][c]), x[d+1][c])
            options2 = []
            for c2 in cities:
                if c2 != c:
                    pair = (min(c, c2), max(c, c2))
                    if pair in flight_pairs:
                        options2.append(And(x[d][c2]))
            if options2:
                s.add(Implies(cond2, Or(options2)))
            else:
                s.add(Not(cond2))
    
    # Constraint 5: Event constraints
    for city, event_days in events.items():
        s.add(Or([x[d][city] for d in event_days]))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in days:
            for c in cities:
                if is_true(model.eval(x[d][c])):
                    itinerary.append({"day": d, "city": c})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()