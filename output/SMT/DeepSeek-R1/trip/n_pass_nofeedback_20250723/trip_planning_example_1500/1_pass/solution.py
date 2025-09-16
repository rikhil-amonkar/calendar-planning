from z3 import *
import json

# Define the cities and their indices
cities = ["London", "Zurich", "Milan", "Reykjavik", "Barcelona", "Bucharest", "Hamburg", "Stuttgart", "Stockholm", "Tallinn"]
n_cities = len(cities)
city_index = {city: idx for idx, city in enumerate(cities)}

# Requirements for each city
required_days = {
    "London": 3,
    "Zurich": 2,
    "Milan": 5,
    "Reykjavik": 5,
    "Barcelona": 4,
    "Bucharest": 2,
    "Hamburg": 5,
    "Stuttgart": 5,
    "Stockholm": 2,
    "Tallinn": 4
}

# Direct flights as an undirected graph
flight_list = [
    ("London", "Hamburg"),
    ("London", "Reykjavik"),
    ("Milan", "Barcelona"),
    ("Reykjavik", "Barcelona"),
    ("Reykjavik", "Stuttgart"),
    ("Stockholm", "Reykjavik"),
    ("London", "Stuttgart"),
    ("Milan", "Zurich"),
    ("London", "Barcelona"),
    ("Stockholm", "Hamburg"),
    ("Zurich", "Barcelona"),
    ("Stockholm", "Stuttgart"),
    ("Milan", "Hamburg"),
    ("Stockholm", "Tallinn"),
    ("Hamburg", "Bucharest"),
    ("London", "Bucharest"),
    ("Milan", "Stockholm"),
    ("Stuttgart", "Hamburg"),
    ("London", "Zurich"),
    ("Milan", "Reykjavik"),
    ("London", "Stockholm"),
    ("Milan", "Stuttgart"),
    ("Stockholm", "Barcelona"),
    ("London", "Milan"),
    ("Zurich", "Hamburg"),
    ("Bucharest", "Barcelona"),
    ("Zurich", "Stockholm"),
    ("Barcelona", "Tallinn"),
    ("Zurich", "Tallinn"),
    ("Hamburg", "Barcelona"),
    ("Stuttgart", "Barcelona"),
    ("Zurich", "Reykjavik"),
    ("Zurich", "Bucharest")
]

# Create a set of edges for the flight graph (undirected)
flight_edges = set()
for flight in flight_list:
    if isinstance(flight, tuple):
        u, v = flight
        flight_edges.add((u, v))
        flight_edges.add((v, u))
    else:
        parts = flight.split(" and ")
        if len(parts) == 2:
            u, v = parts
            flight_edges.add((u, v))
            flight_edges.add((v, u))
        else:
            parts = flight.split(" to ")
            if len(parts) == 2:
                u, v = parts
                flight_edges.add((u, v))
                flight_edges.add((v, u))

# Convert city names to indices in flight_edges_set
flight_edges_set = set()
for u, v in flight_edges:
    if u in city_index and v in city_index:
        flight_edges_set.add((city_index[u], city_index[v]))

# Create Z3 solver
s = Solver()

# Night variables: 29 nights (from night0 to night28)
nights = [Int('night_%d' % i) for i in range(29)]

# Constraint: nights must be between 0 and n_cities-1
for n in nights:
    s.add(n >= 0, n < n_cities)

# Constraint: Start in London (night0)
s.add(nights[0] == city_index["London"])

# Flight constraints: if night_i != night_{i-1}, then (night_{i-1}, night_i) must be in flight_edges_set
for i in range(1, 29):
    prev_night = nights[i-1]
    curr_night = nights[i]
    s.add(If(prev_night != curr_night,
             Or([And(prev_night == u, curr_night == v) for (u, v) in flight_edges_set]),
             True))

# Total days per city: for each city, count the days d (from 1 to 28) such that 
# the traveler is in the city on day d (i.e., night[d-1]==city or night[d]==city)
total_days_per_city = [0] * n_cities
for city in range(n_cities):
    in_city_days = [Bool(f'in_{cities[city]}_day_{d}') for d in range(1, 29)]
    for d in range(1, 29):
        s.add(in_city_days[d-1] == Or(nights[d-1] == city, nights[d] == city))
    total_days_per_city[city] = Sum([If(in_city_days[d], 1, 0) for d in range(28)])
    s.add(total_days_per_city[city] == required_days[cities[city]])

# Special constraints for fixed events

# Must be in Zurich on day7 and day8
s.add(Or(nights[6] == city_index["Zurich"], nights[7] == city_index["Zurich"]))  # day7: night6 or night7
s.add(Or(nights[7] == city_index["Zurich"], nights[8] == city_index["Zurich"]))  # day8: night7 or night8

# Must be in Reykjavik on day9,10,11,12,13
for d in [9,10,11,12,13]:
    # day d: night[d-1] or night[d] must be Reykjavik
    s.add(Or(nights[d-1] == city_index["Reykjavik"], nights[d] == city_index["Reykjavik"]))

# Must be in Milan on at least one day between 3 and 7 (inclusive)
days_in_milan_range = []
for d in range(3, 8):  # days 3 to 7
    # Create condition for being in Milan on day d
    in_milan = Or(nights[d-1] == city_index["Milan"], nights[d] == city_index["Milan"])
    days_in_milan_range.append(in_milan)
s.add(Or(days_in_milan_range))

# Solve the problem
if s.check() == sat:
    m = s.model()
    night_values = [m.evaluate(nights[i]).as_long() for i in range(29)]
    
    # Build the itinerary: for each day, the city at the end of the day (night_i)
    itinerary = []
    for d in range(1, 29):
        city_idx = night_values[d]  # at the end of day d, we are in the city of night_d
        itinerary.append({"day": d, "city": cities[city_idx]})
    
    # Create the JSON output
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")