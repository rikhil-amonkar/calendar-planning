from z3 import Solver, Int, And, Or, If, Sum, sat
import json

# We index the eight cities as follows:
# 0: Riga
# 1: Manchester
# 2: Bucharest
# 3: Florence
# 4: Vienna
# 5: Istanbul
# 6: Reykjavik
# 7: Stuttgart

city_names = {
    0: "Riga",
    1: "Manchester",
    2: "Bucharest",
    3: "Florence",
    4: "Vienna",
    5: "Istanbul",
    6: "Reykjavik",
    7: "Stuttgart"
}

# Required durations.
required_days = {
    0: 4,  # Riga
    1: 5,  # Manchester
    2: 4,  # Bucharest
    3: 4,  # Florence
    4: 2,  # Vienna
    5: 2,  # Istanbul
    6: 4,  # Reykjavik
    7: 5   # Stuttgart
}

# Allowed direct flights.
# (a, b) means a flight can go from city a to city b.
# Most flights are bidirectional (so we include both),
# except "from Reykjavik to Stuttgart" which is one–directional.
allowed_flights = [
    (2, 4), (4, 2),             # Bucharest and Vienna
    (6, 4), (4, 6),             # Reykjavik and Vienna
    (1, 4), (4, 1),             # Manchester and Vienna
    (1, 0), (0, 1),             # Manchester and Riga
    (0, 4), (4, 0),             # Riga and Vienna
    (5, 4), (4, 5),             # Istanbul and Vienna
    (4, 3), (3, 4),             # Vienna and Florence
    (7, 4), (4, 7),             # Stuttgart and Vienna
    (0, 2), (2, 0),             # Riga and Bucharest
    (5, 0), (0, 5),             # Istanbul and Riga
    (7, 5), (5, 7),             # Stuttgart and Istanbul
    (6, 7),                    # from Reykjavik to Stuttgart only
    (5, 2), (2, 5),             # Istanbul and Bucharest
    (1, 5), (5, 1),             # Manchester and Istanbul
    (1, 2), (2, 1),             # Manchester and Bucharest
    (7, 1), (1, 7)              # Stuttgart and Manchester
]

# Number of days in the trip.
num_days = 23

# Create a solver.
s = Solver()

# Create itinerary variables: itinerary[i] is the city on day i+1.
itinerary = [Int(f"day_{i+1}") for i in range(num_days)]
for day in itinerary:
    s.add(day >= 0, day <= 7)

# For each day (after the first), if the city changes then we require that
# the flight from itinerary[i-1] to itinerary[i] is allowed.
for i in range(1, num_days):
    # If there is a flight (i.e. city changes)
    s.add(Or(itinerary[i] == itinerary[i-1],
             Or([And(itinerary[i-1] == a, itinerary[i] == b) for (a, b) in allowed_flights])
            ))

# Exactly 7 flight transitions must occur.
flight_indicators = [If(itinerary[i] != itinerary[i-1], 1, 0) for i in range(1, num_days)]
s.add(Sum(flight_indicators) == 7)

# Count the number of days credited to each city.
# Rule: Day 1 fully counts for the city (1 credit).
# On each subsequent day:
#    - if you stay (itinerary[i] == itinerary[i-1]), you get 1 credit for that city.
#    - if you fly (itinerary[i] != itinerary[i-1]), then that day counts for BOTH:
#         the arrival city gets 1 credit and the departure city (itinerary[i-1]) gains an extra credit.
for city in range(8):
    count_city = If(itinerary[0] == city, 1, 0)
    for i in range(1, num_days):
        # Always add credit for being in the city on day i.
        credit = If(itinerary[i] == city, 1, 0)
        # If there’s a flight on day i, add extra credit for the departure city.
        credit += If(And(itinerary[i] != itinerary[i-1], itinerary[i-1] == city), 1, 0)
        count_city = count_city + credit
    s.add(count_city == required_days[city])

# Special event constraints:
# 1. The annual show in Istanbul is from day 12 to day 13.
#    We force day 12 and day 13 (i.e. itinerary indices 11 and 12) to be Istanbul.
s.add(itinerary[11] == 5)  # day 12 must be Istanbul
s.add(itinerary[12] == 5)  # day 13 must be Istanbul

# 2. Workshop in Bucharest must be attended sometime between day 16 and 19.
#    Recall that if you fly on day d and the flight departs from Bucharest then day d counts as Bucharest.
#    Thus, for at least one d in {16,17,18,19} (i.e. indices 15,16,17,18) we require
#    either the arrival city is Bucharest or (if flying) the departure city is Bucharest.
workshop_options = []
for i in [15, 16, 17, 18]:
    # (itinerary[i] == 2) means you are in Bucharest on day i+1.
    # Or if a flight happens on day i+1 then the departure city (itinerary[i-1]) might be Bucharest.
    workshop_options.append(Or(itinerary[i] == 2, And(itinerary[i] != itinerary[i-1], itinerary[i-1] == 2)))
s.add(Or(workshop_options))

# Now check for a solution.
if s.check() == sat:
    model = s.model()
    sol_itinerary = [model.evaluate(itinerary[i]) for i in range(num_days)]
    # Build the day-place mapping list.
    output = {"itinerary": []}
    for i, city_val in enumerate(sol_itinerary):
        # Day numbers are 1-indexed.
        day_entry = {"day": i+1, "place": city_names[int(city_val.as_long())]}
        output["itinerary"].append(day_entry)
    # Print the JSON output.
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")