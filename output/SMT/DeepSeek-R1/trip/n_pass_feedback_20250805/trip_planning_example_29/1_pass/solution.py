from z3 import *
import json

# Create solver
s = Solver()

# Days and cities
days = list(range(1, 11))
cities = ['D', 'F', 'K']  # D: Dubrovnik, F: Frankfurt, K: Krakow

# in_city[day][city]: True if in city on day
in_city = {}
for day in days:
    for city in cities:
        in_city[(day, city)] = Bool(f"in_{day}_{city}")

# Constraints

# Must be in Krakow on day 9 and 10
s.add(in_city[(9, 'K')] == True)
s.add(in_city[(10, 'K')] == True)

# Total days per city: Dubrovnik 7, Frankfurt 3, Krakow 2
s.add(Sum([If(in_city[(d, 'D')], 1, 0) for d in days]) == 7)
s.add(Sum([If(in_city[(d, 'F')], 1, 0) for d in days]) == 3)
s.add(Sum([If(in_city[(d, 'K')], 1, 0) for d in days]) == 2)

# Each day: in 1 or 2 cities, and exactly 2 days with 2 cities
two_city_days = []
for day in days:
    num_cities = Sum([If(in_city[(day, c)], 1, 0) for c in cities])
    s.add(Or(num_cities == 1, num_cities == 2))
    two_city_days.append(If(num_cities == 2, 1, 0))
s.add(Sum(two_city_days) == 2)

# Adjacent cities for flights
adjacent_pairs = [('D', 'F'), ('F', 'D'), ('F', 'K'), ('K', 'F')]

# Continuity constraints for consecutive days
for i in range(1, 10):
    changes = []
    for city in cities:
        added = And(Not(in_city[(i, city)]), in_city[(i+1, city)])
        removed = And(in_city[(i, city)], Not(in_city[(i+1, city)]))
        changes.append(Or(added, removed))
        
        # If added, must be adjacent to a city present on day i
        if added is not None:
            adjacent_exists = Or([And(in_city[(i, other)], (other, city) in adjacent_pairs) for other in cities if other != city])
            s.add(Implies(added, adjacent_exists))
        
        # If removed, must be adjacent to a city present on day i+1
        if removed is not None:
            adjacent_exists_next = Or([And(in_city[(i+1, other)], (city, other) in adjacent_pairs) for other in cities if other != city])
            s.add(Implies(removed, adjacent_exists_next))
    
    # At most one change per day (either one added or one removed)
    s.add(Sum([If(c, 1, 0) for c in changes]) <= 1)

# Solve the problem
if s.check() == sat:
    m = s.model()
    itinerary_list = []
    for day in days:
        for city in cities:
            if is_true(m.evaluate(in_city[(day, city)])):
                if city == 'D':
                    city_name = "Dubrovnik"
                elif city == 'F':
                    city_name = "Frankfurt"
                else:
                    city_name = "Krakow"
                itinerary_list.append({"day": day, "city": city_name})
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')