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
    ("Zurich", "Hamburg"), ("Hamburg", "Zurich"),  # Note: Zurich is spelled as "Zurich" in the problem
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
    8: ["Zurich", "Barcelona"],  # We choose Barcelona for city X
    9: ["Barcelona", "Reykjavik"],
    10: ["Reykjavik"],
    11: ["Reykjavik"],
    12: ["Reykjavik"],
    13: ["Reykjavik", "Barcelona"]  # We choose to fly to Barcelona on day13 to avoid extra day in Reykjavik
}

# Adjust the required days for cities that appear in the fixed assignments
adjusted_required_days = required_days.copy()
adjusted_required_days["Barcelona"] -= 3  # 2 days (day8 and day9) + 1 day (day13) = 3 days
adjusted_required_days["Reykjavik"] = 5  # Already satisfied by days 9-13
adjusted_required_days["London"] = 3  # Satisfied
adjusted_required_days["Milan"] = 5  # Satisfied
adjusted_required_days["Zurich"] = 2  # Satisfied

# Days for the variable part: 14 to 28
start_var_day = 14
end_day = 28
var_days = list(range(start_var_day, end_day + 1))
num_var_days = len(var_days)

# Cities for the variable part: all except those that are already fully satisfied and won't be visited again
# We exclude London, Zurich, Milan, Reykjavik (since we are done with them)
# But note: we are including Barcelona (which needs 1 more day) and the others
variable_cities = ["Bucharest", "Hamburg", "Barcelona", "Stuttgart", "Stockholm", "Tallinn"]

# Create a Z3 solver
s = Solver()

# Create a dictionary of in_city variables: in_city[city][day] for days 14 to 28
in_city = {}
for city in variable_cities:
    in_city[city] = {}
    for day in var_days:
        in_city[city][day] = Bool(f"in_{city}_{day}")

# Also, we need to model flights between these cities on these days.
# But note: we also have to fly from a city to another, and we start from Barcelona on day13 (end of day13) and then we are in Barcelona on day14? 
# However, on day13 we are in Reykjavik and Barcelona. Then on day14, we are in Barcelona (if we stay) or we fly to another city.

# We will create flight variables for each day from 14 to 28, and for each pair of distinct cities (c1, c2) if there is a direct flight.
# But note: flights on day d imply that on day d, we are in c1 and c2, and not in other cities.

# However, to reduce variables, we can use the following:
# Let flight_day[d] be an array of boolean variables for each possible flight on day d.

# We'll create a variable for each day d and for each pair (c1, c2) that has a direct flight, but note: we have 6 cities, so 6*5=30 directed pairs? but not all have direct flights.

# Instead, we can create a variable for each day and for each ordered pair (c1, c2) in the direct_flights that are among the variable_cities or from Barcelona (since we start in Barcelona on day14).

# But wait, we start in Barcelona at the end of day13? so for day14, we are in Barcelona. We may stay or fly.

# We'll define flight variables for:
#   For day in var_days, and for (c1, c2) in direct_flights, such that c1 and c2 are in variable_cities (or including Reykjavik? but we are done with Reykjavik, so no).

# However, note we are only dealing with the 6 cities.

# Let's get the directed flights among the variable_cities that are in the direct_flights set.
directed_flights_variable = []
for c1 in variable_cities:
    for c2 in variable_cities:
        if c1 != c2:
            if (c1, c2) in direct_flights:
                directed_flights_variable.append((c1, c2))
            # Also check bidirectional? but our direct_flights set has both directions if bidirectional? so we have both (c1,c2) and (c2,c1) if bidirectional.

# But note: the flight from Reykjavik to Stuttgart is directional, but Reykjavik is not in variable_cities, so we skip.

# We'll create a flight variable for each day in var_days and each directed flight in directed_flights_variable.
flight_vars = {}
for day in var_days:
    for (c1, c2) in directed_flights_variable:
        flight_vars[(day, c1, c2)] = Bool(f"flight_{day}_{c1}_{c2}")

# Constraints:

# 1. Each day, we are in at least one city? But we start in Barcelona on day14? and we might fly, so we are always in at least one city.

# 2. For each city, the total days (including the fixed part) must equal the required days.
#    For the variable part, we sum the days in the variable period.
for city in variable_cities:
    total_days = adjusted_required_days[city]
    # If total_days is 0, then we should not be in that city in the variable period.
    if total_days == 0:
        for day in var_days:
            s.add(Not(in_city[city][day]))
    else:
        # Sum the days in the variable period
        s.add(sum([If(in_city[city][day], 1, 0) for day in var_days]) == total_days)

# 3. On each day, we are in at least one city? Actually, we are in exactly one or two cities? 
#    But note: if we fly, we are in two cities; if we stay, we are in one.
#    However, we start each day in one city, and then if we fly, we are in two.
for day in var_days:
    # List of variables for being in each city on this day
    in_vars = [in_city[city][day] for city in variable_cities]
    # At least one city? 
    s.add(Or(*in_vars))
    # At most two? 
    # We can have more than two if we have multiple flights? but we only allow one flight per day.
    # So we have either 1 or 2.
    # Instead, we enforce: the number of True in_vars is 1 or 2.
    s.add(Or(
        Sum([If(v, 1, 0) for v in in_vars]) == 1,
        Sum([If(v, 1, 0) for v in in_vars]) == 2
    ))

# 4. Flight constraints:
#    a. If there is a flight on day d from c1 to c2, then on day d we are in c1 and in c2.
for day in var_days:
    for (c1, c2) in directed_flights_variable:
        flight_var = flight_vars[(day, c1, c2)]
        s.add(Implies(flight_var, And(in_city[c1][day], in_city[c2][day])))
        # Also, if we are in c1 and c2 on day d, and there is a direct flight, it doesn't necessarily mean we flew that day? 
        # But we can have other reasons? like we stayed in c1 and also flew from somewhere else to c2? 
        # However, we have the constraint that we are in at most two cities? so if we are in c1 and c2, then there is a flight between them? 
        # But it could be from c2 to c1? 
        # We'll add: if we are in two cities c1 and c2 on day d, then there must be a flight between them (in one direction or the other) on that day.
        # But note: we have flight variables for both directions? 
        s.add(Implies(And(in_city[c1][day], in_city[c2][day]), 
                    Or(flight_vars.get((day, c1, c2), False), 
                       flight_vars.get((day, c2, c1), False) if (day, c2, c1) in flight_vars else False)))

    # b. For a flight to occur, there must be a direct flight (we already have the flight_vars only for existing direct flights, so this is inherent).

    # c. At most one flight per day? 
    flight_vars_this_day = [flight_vars[(day, c1, c2)] for (c1, c2) in directed_flights_variable if (day, c1, c2) in flight_vars]
    s.add(AtMost(*flight_vars_this_day, 1))

# 5. Connectivity: 
#    For a city c and day d (from 14 to 27), if we are in c on day d and not in c on day d+1, then there must be a flight from c to some city on day d+1.
#    Similarly, if we are not in c on day d and in c on day d+1, then there must be a flight to c from some city on day d+1.
for city in variable_cities:
    for day in var_days:
        if day < end_day:  # day+1 is in var_days or beyond? but var_days only to 28, so day from 14 to 27
            # If in city on day and not on day+1, then there is a flight from city to some c2 on day+1.
            in_today = in_city[city][day]
            in_next = in_city[city][day+1]
            # Leave city: in_today and not in_next
            leave = And(in_today, Not(in_next))
            # Then there must be a flight from city to some c2 on day+1
            flight_out_exists = Or([flight_vars.get((day+1, city, c2), False) for c2 in variable_cities if c2 != city and (day+1, city, c2) in flight_vars])
            s.add(Implies(leave, flight_out_exists))

            # Arrive in city: not in_today and in_next
            arrive = And(Not(in_today), in_next)
            flight_in_exists = Or([flight_vars.get((day+1, c2, city), False) for c2 in variable_cities if c2 != city and (day+1, c2, city) in flight_vars])
            s.add(Implies(arrive, flight_in_exists))

# 6. We start on day14 in Barcelona? because at the end of day13 we are in Barcelona.
#    So on day14, we must be in Barcelona (unless we fly on day14, then we are in Barcelona and another city).
#    But we have the fixed assignment for day13: we are in Barcelona on day13.
#    And for day14: 
#        Since we are in Barcelona on day13, and we don't have day14 in the fixed part, we need to decide.
#        We can stay in Barcelona on day14? or fly to another city on day14.
#    So we require: in_city["Barcelona"][14] is True? because we are there at the start of the day? 
#    But if we fly, we will also be in the arrival city on day14.
s.add(in_city["Barcelona"][14] == True)

# Solve the model
if s.check() == sat:
    m = s.model()
    # Build the itinerary for days 14 to 28
    itinerary = []

    # First, add the fixed part for days 1 to 13
    for day in range(1, 14):
        cities_today = fixed_assignments[day]
        if len(cities_today) == 1:
            itinerary.append({"day_range": f"Day {day}", "place": cities_today[0]})
        else:
            # Flight day: add both
            for city in cities_today:
                itinerary.append({"day_range": f"Day {day}", "place": city})

    # Now, for the variable part: days 14 to 28
    # We need to group consecutive days for the same city to create day ranges? but note: we have to break at flights.
    # The problem requires: for flight days, we must list the day separately for each city, and then the stay as a range.

    # We'll create a list for each day: the cities we are in that day.
    schedule = {}
    for day in var_days:
        schedule[day] = []
        for city in variable_cities:
            if is_true(m.eval(in_city[city][day])):
                schedule[day].append(city)

    # Now, we want to create the itinerary with ranges.
    # For each city, we want to find consecutive days? but note: a city might appear non consecutively.
    # Instead, we can traverse day by day.

    # We'll create a list of events: for each day, and for each city we are in that day, we have an event.
    # But the problem requires: 
    #   For flight days, create separate records for both the departure and arrival city, and also the stay ranges.
    # Example: 
    #   If we are in Venice from day1 to day3 and fly to Vienna on day3, then:
    #       {"day_range": "Day 1-3", "place": "Venice"}
    #       {"day_range": "Day 3", "place": "Venice"}
    #       {"day_range": "Day 3", "place": "Vienna"}
    #       {"day_range": "Day 3-5", "place": "Vienna"}
    #
    # How to do this? 
    #   We can break each stay in a city into contiguous blocks. For the last day of a block, if it is a flight day (and the city appears only on that day in the block as a flight day) then we break it as a single day.

    # However, to simplify, we can output:
    #   For each city and for each contiguous block of days (even if one day) we output a range for the entire block (from start to end) and then if the last day is a flight day, we also output a single day for the last day? 
    #   But note the example: 
    #       Venice: [1,2,3] -> we output "Day 1-3" and then also "Day 3" separately? 
    #   That seems redundant? 

    # Alternatively, we can output:
    #   For every day and every city: an entry for that day and that city.
    #   But the problem example: 
    #       {"day_range": "Day 1-3", "place": "Venice"}   -> this is the stay
    #       and then separately for the flight day: 
    #       {"day_range": "Day 3", "place": "Venice"} 
    #       {"day_range": "Day 3", "place": "Vienna"} 
    #   So the day3 appears three times? 

    # How they are derived?
    #   The stay in Venice is from day1 to day3 -> so a range 1-3.
    #   Then, on the flight day (day3), they list the departure (Venice) and the arrival (Vienna) as single day entries.
    #   Then the stay in Vienna from day3 to day5 -> a range 3-5.

    # So the algorithm:
    #   We'll first create the stay ranges: for each city, find contiguous days.
    #   Then, for each contiguous block (say from start to end), we output:
    #        {"day_range": f"Day {start}-{end}", "place": city}
    #   Then, for every flight day (every day where there is a flight, i.e., two cities) we output for each city in that day:
    #        {"day_range": f"Day {day}", "place": city}
    #   But note: the flight day might be the last day of a stay? then we have both the range and the single day.

    # However, the fixed part already has the flight days broken out? so we do the same for the variable part.

    # We'll do:
    #   For the variable part (days 14 to 28), we'll create:
    #       1. All the contiguous blocks for each city (without breaking flight days) and output the range.
    #       2. Then, for each day that is a flight day (i.e., two cities) we output a single day for each city in that day.

    # But note: a day might be a flight day and also the last day of a stay? then we output the range and then the single day.

    # Step 1: Find contiguous blocks per city.
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

    # Step 2: Output the blocks as ranges.
    for city in variable_cities:
        for (start, end) in blocks[city]:
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    # Step 3: For each day in the variable part that has exactly two cities, output a single day for each city.
    for day in var_days:
        cities_today = schedule[day]
        if len(cities_today) == 2:
            for city in cities_today:
                itinerary.append({"day_range": f"Day {day}", "place": city})

    # Now, we have the itinerary. We must sort by the day_range? 
    # But the problem doesn't specify order? but we can sort by the start day of the range? or by the day.

    # We'll convert the day_range string to a tuple of integers for sorting.
    def day_key(entry):
        s = entry['day_range']
        if '-' in s:
            parts = s.split(' ')[1].split('-')
            return (int(parts[0]), 0)  # start day, and then we break ties arbitrarily
        else:
            day = int(s.split(' ')[1])
            return (day, 1)   # single day after ranges? but the example: the flight day single day is after the range? 

    itinerary_sorted = sorted(itinerary, key=day_key)

    # Output as JSON
    result = {"itinerary": itinerary_sorted}
    print(json.dumps(result))
else:
    print("No solution found")