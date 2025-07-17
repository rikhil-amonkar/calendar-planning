from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Correct city names
    cities_corrected = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    cities = cities_corrected
    
    # Flight pairs as per the problem statement
    flight_pairs = [
        ('Helsinki', 'London'),
        ('Split', 'Madrid'),
        ('Helsinki', 'Madrid'),  # Assuming this is Helsinki
        ('London', 'Madrid'),
        ('Brussels', 'London'),
        ('Bucharest', 'London'),
        ('Brussels', 'Bucharest'),
        ('Bucharest', 'Madrid'),
        ('Split', 'Helsinki'),
        ('Mykonos', 'Madrid'),
        ('Stuttgart', 'London'),
        ('Helsinki', 'Brussels'),
        ('Brussels', 'Madrid'),
        ('Split', 'London'),
        ('Stuttgart', 'Split'),
        ('London', 'Mykonos')
    ]
    
    # Correct any typos in flight_pairs
    corrected_flight_pairs = []
    for a, b in flight_pairs:
        if a == 'Helsinki':
            pass
        elif a == 'Helsinki':
            a = 'Helsinki'
        if b == 'Madrid':
            pass
        elif b == 'Madrid':
            b = 'Madrid'
        corrected_flight_pairs.append((a, b))
    flight_pairs = corrected_flight_pairs
    
    # Build adjacency list
    adjacency = {city: [] for city in cities}
    for a, b in flight_pairs:
        if a in cities and b in cities:
            if b not in adjacency[a]:
                adjacency[a].append(b)
            if a not in adjacency[b]:
                adjacency[b].append(a)
    
    # Days are 1..21
    days = 21
    day_numbers = list(range(1, days + 1))
    
    # Create a Z3 solver
    s = Solver()
    
    # Create variables: day[i] represents the city on day i (1-based)
    city_list = sorted(cities.keys())
    city_to_num = {city: idx for idx, city in enumerate(city_list)}
    num_to_city = {idx: city for city, idx in city_to_num.items()}
    
    day_vars = [Int(f"day_{i}") for i in day_numbers]
    
    # Each day_var must be one of the cities (encoded as integers)
    for d in day_vars:
        s.add(Or([d == city_to_num[city] for city in city_list]))
    
    # Constraint: Madrid must be days 20 and 21
    s.add(day_vars[19] == city_to_num['Madrid'])  # day 20 is index 19 (0-based)
    s.add(day_vars[20] == city_to_num['Madrid'])  # day 21
    
    # Constraint: Stuttgart must be visited between day 1 and 4 (inclusive)
    s.add(Or([day_vars[i] == city_to_num['Stuttgart'] for i in range(4)]))  # days 1-4 (indices 0-3)
    
    # Constraint: transitions between days must be valid flights or same city
    for i in range(days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        # Either stay in the same city or move to a directly connected city
        possible_transitions = []
        # Same city
        possible_transitions.append(current_city == next_city)
        # Direct flights
        for city in city_list:
            for neighbor in adjacency.get(city, []):
                possible_transitions.append(
                    And(current_city == city_to_num[city], next_city == city_to_num[neighbor])
                )
        s.add(Or(possible_transitions))
    
    # Constraint: total days per city must match requirements
    for city in city_list:
        total_days = cities[city]
        occurrences = Sum([If(day_vars[i] == city_to_num[city], 1, 0) for i in range(days)])
        s.add(occurrences == total_days)
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in day_numbers:
            city_num = model.evaluate(day_vars[day - 1]).as_long()
            city = num_to_city[city_num]
            itinerary.append({"day": day, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))