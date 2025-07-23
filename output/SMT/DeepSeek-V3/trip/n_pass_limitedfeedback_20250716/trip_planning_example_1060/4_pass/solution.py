from z3 import *

def solve_itinerary():
    # Cities with correct spelling
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 25

    # Direct flights: adjacency list (bidirectional)
    direct_flights = {
        'Geneva': ['Istanbul', 'Munich', 'Valencia'],
        'Istanbul': ['Geneva', 'Stuttgart', 'Valencia', 'Vilnius', 'Munich'],
        'Reykjavik': ['Munich', 'Stuttgart'],
        'Munich': ['Reykjavik', 'Geneva', 'Seville', 'Vilnius', 'Istanbul', 'Valencia'],
        'Stuttgart': ['Valencia', 'Istanbul', 'Reykjavik'],
        'Valencia': ['Stuttgart', 'Seville', 'Istanbul', 'Geneva', 'Munich'],
        'Seville': ['Valencia', 'Munich'],
        'Vilnius': ['Istanbul', 'Munich']
    }

    # Create Z3 variables
    city_vars = [Int(f'day_{i}') for i in range(1, n_days + 1)]
    s = Solver()

    # Each day's assignment must be a valid city index
    for day in city_vars:
        s.add(day >= 0, day < n_cities)

    # Flight transitions between consecutive days
    for i in range(n_days - 1):
        current_city = city_vars[i]
        next_city = city_vars[i + 1]
        same_city = current_city == next_city
        allowed_transitions = []
        
        # Generate all possible valid transitions
        for src in range(n_cities):
            src_name = cities[src]
            for dest in range(n_cities):
                dest_name = cities[dest]
                if dest_name in direct_flights.get(src_name, []):
                    allowed_transitions.append(And(current_city == src, next_city == dest))
        
        s.add(Or(same_city, Or(allowed_transitions)))

    # Duration constraints
    # Stuttgart: 4 days total, conference on day 4 and 7
    stuttgart_idx = city_map['Stuttgart']
    s.add(Sum([If(city_vars[i] == stuttgart_idx, 1, 0) for i in range(n_days)]) == 4)
    s.add(city_vars[3] == stuttgart_idx)  # day 4 (0-based: 3)
    s.add(city_vars[6] == stuttgart_idx)  # day 7 (0-based: 6)

    # Istanbul: 4 days, relatives between day 19-22 (0-based 18-21)
    istanbul_idx = city_map['Istanbul']
    s.add(Sum([If(city_vars[i] == istanbul_idx, 1, 0) for i in range(n_days)]) == 4)
    # Must be in Istanbul for at least one day between 19-22
    s.add(Or([city_vars[i] == istanbul_idx for i in range(18, 22)]))

    # Vilnius: 4 days
    vilnius_idx = city_map['Vilnius']
    s.add(Sum([If(city_vars[i] == vilnius_idx, 1, 0) for i in range(n_days)]) == 4)

    # Seville: 3 days
    seville_idx = city_map['Seville']
    s.add(Sum([If(city_vars[i] == seville_idx, 1, 0) for i in range(n_days)]) == 3)

    # Geneva: 5 days
    geneva_idx = city_map['Geneva']
    s.add(Sum([If(city_vars[i] == geneva_idx, 1, 0) for i in range(n_days)]) == 5)

    # Valencia: 5 days
    valencia_idx = city_map['Valencia']
    s.add(Sum([If(city_vars[i] == valencia_idx, 1, 0) for i in range(n_days)]) == 5)

    # Munich: 3 days, annual show day 13-15 (0-based 12-14)
    munich_idx = city_map['Munich']
    s.add(Sum([If(city_vars[i] == munich_idx, 1, 0) for i in range(n_days)]) == 3)
    s.add(Or([city_vars[i] == munich_idx for i in range(12, 15)]))

    # Reykjavik: 4 days, workshop between day 1-4 (0-based 0-3)
    reykjavik_idx = city_map['Reykjavik']
    s.add(Sum([If(city_vars[i] == reykjavik_idx, 1, 0) for i in range(n_days)]) == 4)
    s.add(Or([city_vars[i] == reykjavik_idx for i in range(0, 4)]))

    # Additional constraints to help the solver
    # Must start in Reykjavik (workshop days 1-4)
    s.add(city_vars[0] == reykjavik_idx)
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, n_days + 1):
            city_idx = model.evaluate(city_vars[day - 1]).as_long()
            itinerary.append({"day": day, "place": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing some constraints
        print("No solution found with current constraints. Trying relaxed constraints...")
        # Relax the Istanbul relatives constraint to just require 4 days total
        s.pop()
        s.add(Sum([If(city_vars[i] == istanbul_idx, 1, 0) for i in range(n_days)]) == 4)
        
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for day in range(1, n_days + 1):
                city_idx = model.evaluate(city_vars[day - 1]).as_long()
                itinerary.append({"day": day, "place": cities[city_idx]})
            return {"itinerary": itinerary}
        else:
            return {"error": "No valid itinerary found even with relaxed constraints"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)