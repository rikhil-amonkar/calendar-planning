from z3 import *

def solve_itinerary():
    # Cities with their required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,  # Conference on days 20-21
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # All direct flight connections (bidirectional)
    flight_connections = [
        ('Helsinki', 'London'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Brussels'),
        ('Helsinki', 'Split'),
        ('Split', 'Madrid'),
        ('Split', 'London'),
        ('Split', 'Stuttgart'),
        ('Madrid', 'London'),
        ('Madrid', 'Mykonos'),
        ('Madrid', 'Bucharest'),
        ('Madrid', 'Brussels'),
        ('London', 'Brussels'),
        ('London', 'Bucharest'),
        ('London', 'Mykonos'),
        ('London', 'Stuttgart'),
        ('Brussels', 'Bucharest'),
        ('Brussels', 'Madrid'),
        ('Bucharest', 'Madrid'),
        ('Stuttgart', 'London'),
        ('Stuttgart', 'Split'),
        ('Mykonos', 'Madrid'),
        ('Mykonos', 'London')
    ]

    # Create mappings between city names and integers
    city_list = sorted(cities.keys())  # Sort for consistent ordering
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    int_to_city = {idx: city for idx, city in enumerate(city_list)}

    # Days in the itinerary (1-21)
    total_days = 21
    
    # Create Z3 variables for each day's city
    day_city = [Int(f'day_{i+1}') for i in range(total_days)]
    
    s = Solver()

    # 1. Each day must be assigned a valid city
    for dc in day_city:
        s.add(dc >= 0, dc < len(city_list))

    # 2. Flight constraints between consecutive days
    # Precompute all allowed transitions (including staying in same city)
    allowed_transitions = []
    # Add staying in same city
    for city in city_list:
        allowed_transitions.append((city_to_int[city], city_to_int[city]))
    # Add all flight connections (both directions)
    for c1, c2 in flight_connections:
        allowed_transitions.append((city_to_int[c1], city_to_int[c2]))
        allowed_transitions.append((city_to_int[c2], city_to_int[c1]))

    for i in range(total_days - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        # Create disjunction of all allowed transitions
        transition_constraints = []
        for (c1, c2) in allowed_transitions:
            transition_constraints.append(And(current == c1, next_c == c2))
        s.add(Or(transition_constraints))

    # 3. Duration constraints for each city
    for city, days_needed in cities.items():
        s.add(Sum([If(day_city[i] == city_to_int[city], 1, 0) 
              for i in range(total_days)]) == days_needed)

    # 4. Special constraints
    # Conference in Madrid on days 20-21 (indices 19-20)
    s.add(day_city[19] == city_to_int['Madrid'])
    s.add(day_city[20] == city_to_int['Madrid'])
    
    # Visit Stuttgart between days 1-4 (indices 0-3)
    s.add(Or([day_city[i] == city_to_int['Stuttgart'] for i in range(4)]))

    # 5. Additional constraints to help guide the solver
    # Ensure we don't have impossible single-day visits when flights are needed
    for i in range(1, total_days - 1):
        prev = day_city[i-1]
        curr = day_city[i]
        next_c = day_city[i+1]
        # If current city is different from both previous and next, it must have flights to both
        s.add(Implies(And(curr != prev, curr != next_c),
                     Or([And(prev == city_to_int[c1], curr == city_to_int[c2]) 
                         for (c1, c2) in flight_connections] +
                        [And(curr == city_to_int[c1], next_c == city_to_int[c2]) 
                         for (c1, c2) in flight_connections])))

    # Try to find a solution with a time limit
    s.set("timeout", 30000)  # 30 seconds timeout
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = model.evaluate(day_city[i]).as_long()
            city_name = int_to_city[city_idx]
            itinerary.append({'day': i+1, 'place': city_name})
        
        # Verify the solution
        counts = {city: 0 for city in cities}
        flight_days = set()
        for i in range(total_days):
            counts[itinerary[i]['place']] += 1
            if i > 0 and itinerary[i]['place'] != itinerary[i-1]['place']:
                flight_days.add(i+1)  # Flight on this day
        
        print("Verification:")
        for city, cnt in counts.items():
            print(f"{city}: {cnt} days (required: {cities[city]})")
        print(f"Flight days: {sorted(flight_days)}")
        
        return {'itinerary': itinerary}
    else:
        print("Failed to find a valid itinerary")
        print("Possible reasons:")
        print("- Constraints may be too restrictive")
        print("- Not enough days to visit all cities with required durations")
        print("- Flight connections may not support the required itinerary")
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))