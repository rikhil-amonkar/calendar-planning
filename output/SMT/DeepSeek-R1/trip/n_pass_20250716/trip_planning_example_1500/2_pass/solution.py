from z3 import *
import json

# Define cities and their required days
cities = ["London", "Zurich", "Bucharest", "Hamburg", "Barcelona", "Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Milan"]
required_days = {
    "London": 3,
    "Zurich": 2,
    "Bucharest": 2,
    "Hamburg": 5,
    "Barcelona": 4,
    "Reykjavik": 5,
    "Stuttgart": 5,
    "Stockholm": 2,
    "Tallinn": 4,
    "Milan": 5
}

# Direct flights: bidirectional unless specified otherwise
direct_flights_list = [
    ("London", "Hamburg"), ("Hamburg", "London"),
    ("London", "Reykjavik"), ("Reykjavik", "London"),
    ("Milan", "Barcelona"), ("Barcelona", "Milan"),
    ("Reykjavik", "Barcelona"), ("Barcelona", "Reykjavik"),
    ("Reykjavik", "Stuttgart"),  # Only from Reykjavik to Stuttgart
    ("Stockholm", "Reykjavik"), ("Reykjavik", "Stockholm"),
    ("London", "Stuttgart"), ("Stuttgart", "London"),
    ("Milan", "Zurich"), ("Zurich", "Milan"),
    ("London", "Barcelona"), ("Barcelona", "London"),
    ("Stockholm", "Hamburg"), ("Hamburg", "Stockholm"),
    ("Zurich", "Barcelona"), ("Barcelona", "Zurich"),
    ("Stockholm", "Stuttgart"), ("Stuttgart", "Stockholm"),
    ("Milan", "Hamburg"), ("Hamburg", "Milan"),
    ("Stockholm", "Tallinn"), ("Tallinn", "Stockholm"),
    ("Hamburg", "Bucharest"), ("Bucharest", "Hamburg"),
    ("London", "Bucharest"), ("Bucharest", "London"),
    ("Milan", "Stockholm"), ("Stockholm", "Milan"),
    ("Stuttgart", "Hamburg"), ("Hamburg", "Stuttgart"),
    ("London", "Zurich"), ("Zurich", "London"),
    ("Milan", "Reykjavik"), ("Reykjavik", "Milan"),
    ("London", "Stockholm"), ("Stockholm", "London"),
    ("Milan", "Stuttgart"), ("Stuttgart", "Milan"),
    ("Stockholm", "Barcelona"), ("Barcelona", "Stockholm"),
    ("London", "Milan"), ("Milan", "London"),
    ("Zurich", "Hamburg"), ("Hamburg", "Zurich"),
    ("Bucharest", "Barcelona"), ("Barcelona", "Bucharest"),
    ("Zurich", "Stockholm"), ("Stockholm", "Zurich"),
    ("Barcelona", "Tallinn"), ("Tallinn", "Barcelona"),
    ("Zurich", "Tallinn"), ("Tallinn", "Zurich"),
    ("Hamburg", "Barcelona"), ("Barcelona", "Hamburg"),
    ("Stuttgart", "Barcelona"), ("Barcelona", "Stuttgart"),
    ("Zurich", "Reykjavik"), ("Reykjavik", "Zurich"),
    ("Zurich", "Bucharest"), ("Bucharest", "Zurich")
]

# Create a set of direct flight pairs
direct_flights = set()
for flight in direct_flights_list:
    direct_flights.add(flight)

# We have fixed days for the first 13 days
fixed_assignments = {
    1: ["London"],
    2: ["London"],
    3: ["London", "Milan"],
    4: ["Milan"],
    5: ["Milan"],
    6: ["Milan"],
    7: ["Milan", "Zurich"],
    8: ["Zurich", "Barcelona"],
    9: ["Barcelona", "Reykjavik"],
    10: ["Reykjavik"],
    11: ["Reykjavik"],
    12: ["Reykjavik"],
    13: ["Reykjavik", "Barcelona"]
}

# Adjust the required days for cities that appear in the fixed assignments
adjusted_required_days = required_days.copy()
adjusted_required_days["Barcelona"] -= 3  # days 8, 9, and 13
adjusted_required_days["Reykjavik"] = 5   # days 9-13
adjusted_required_days["London"] = 3      # days 1-3
adjusted_required_days["Milan"] = 5       # days 3-7
adjusted_required_days["Zurich"] = 2      # days 7-8

# Days for the variable part: 14 to 28
start_var_day = 14
end_day = 28
var_days = list(range(start_var_day, end_day + 1))
num_var_days = len(var_days)

# Cities for the variable part
variable_cities = ["Bucharest", "Hamburg", "Barcelona", "Stuttgart", "Stockholm", "Tallinn"]

# Create a Z3 solver
s = Solver()

# Create a dictionary of in_city variables: in_city[city][day] for days 14 to 28
in_city = {}
for city in variable_cities:
    in_city[city] = {}
    for day in var_days:
        in_city[city][day] = Bool(f"in_{city}_{day}")

# Get the directed flights among the variable_cities
directed_flights_variable = []
for c1 in variable_cities:
    for c2 in variable_cities:
        if c1 != c2 and (c1, c2) in direct_flights:
            directed_flights_variable.append((c1, c2))

# Create flight variables for each day in var_days and each directed flight
flight_vars = {}
for day in var_days:
    for (c1, c2) in directed_flights_variable:
        flight_vars[(day, c1, c2)] = Bool(f"flight_{day}_{c1}_{c2}")

# Constraints:

# 1. Each city must be visited for the adjusted required days in the variable period
for city in variable_cities:
    total_days = adjusted_required_days[city]
    if total_days == 0:
        for day in var_days:
            s.add(Not(in_city[city][day]))
    else:
        s.add(sum([If(in_city[city][day], 1, 0) for day in var_days]) == total_days)

# 2. Each day, we are in at least one and at most two cities
for day in var_days:
    in_vars = [in_city[city][day] for city in variable_cities]
    s.add(Or(*in_vars))  # At least one city
    s.add(Or(Sum([If(v, 1, 0) for v in in_vars]) == 1,
             Sum([If(v, 1, 0) for v in in_vars]) == 2))

# 3. Flight constraints:
#    a. If there is a flight from c1 to c2 on day d, then we are in both c1 and c2 on day d.
#    b. If we are in two cities on day d, there must be a flight between them (in one direction).
#    c. At most one flight per day.
for day in var_days:
    flight_vars_this_day = []
    for (c1, c2) in directed_flights_variable:
        flight_var = flight_vars[(day, c1, c2)]
        flight_vars_this_day.append(flight_var)
        # Flight implies presence in both cities
        s.add(Implies(flight_var, And(in_city[c1][day], in_city[c2][day])))
    # Presence in two cities implies a flight between them
    for i in range(len(variable_cities)):
        for j in range(i+1, len(variable_cities)):
            c1 = variable_cities[i]
            c2 = variable_cities[j]
            if (c1, c2) in directed_flights_variable or (c2, c1) in directed_flights_variable:
                s.add(Implies(And(in_city[c1][day], in_city[c2][day]),
                              Or(flight_vars.get((day, c1, c2), False),
                                 flight_vars.get((day, c2, c1), False))))
    # At most one flight per day
    s.add(AtMost(*flight_vars_this_day, 1))

# 4. Connectivity constraints: flights must connect city presence changes on the same day
for city in variable_cities:
    for day in var_days:
        if day < end_day:  # day+1 exists
            # Leaving city: in today but not tomorrow
            leave = And(in_city[city][day], Not(in_city[city][day+1]))
            flight_out_exists = Or([flight_vars.get((day, city, c2), False) 
                                   for c2 in variable_cities if c2 != city and (day, city, c2) in flight_vars])
            s.add(Implies(leave, flight_out_exists))

            # Arriving in city: not today but tomorrow
            arrive = And(Not(in_city[city][day]), in_city[city][day+1]))
            flight_in_exists = Or([flight_vars.get((day, c2, city), False) 
                                   for c2 in variable_cities if c2 != city and (day, c2, city) in flight_vars])
            s.add(Implies(arrive, flight_in_exists))

# 5. Start on day 14 in Barcelona
s.add(in_city["Barcelona"][14] == True)

# Solve the model
if s.check() == sat:
    m = s.model()
    # Build the itinerary for days 1 to 28
    itinerary = []

    # Add fixed part (days 1-13)
    for day in range(1, 14):
        cities_today = fixed_assignments[day]
        if len(cities_today) == 1:
            itinerary.append({"day_range": f"Day {day}", "place": cities_today[0]})
        else:
            for city in cities_today:
                itinerary.append({"day_range": f"Day {day}", "place": city})

    # For variable part (days 14-28): find contiguous blocks per city
    blocks = {city: [] for city in variable_cities}
    for city in variable_cities:
        in_block = False
        start_block = None
        for day in var_days:
            if is_true(m.eval(in_city[city][day])):
                if not in_block:
                    in_block = True
                    start_block = day
            else:
                if in_block:
                    blocks[city].append((start_block, day-1))
                    in_block = False
        if in_block:
            blocks[city].append((start_block, var_days[-1]))

    # Output contiguous blocks as ranges
    for city in variable_cities:
        for (start, end) in blocks[city]:
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    # Output flight days as separate entries for each city
    for day in var_days:
        cities_today = []
        for city in variable_cities:
            if is_true(m.eval(in_city[city][day])):
                cities_today.append(city)
        if len(cities_today) == 2:  # Flight day
            for city in cities_today:
                itinerary.append({"day_range": f"Day {day}", "place": city})

    # Sort itinerary by day
    def day_key(entry):
        s = entry['day_range']
        if s.startswith('Day'):
            parts = s.split()[1]
            if '-' in parts:
                start, end = map(int, parts.split('-'))
                return (start, 0)
            else:
                day = int(parts)
                return (day, 1)
        return (0, 0)

    itinerary_sorted = sorted(itinerary, key=day_key)
    print(json.dumps({"itinerary": itinerary_sorted}))
else:
    print("No solution found")