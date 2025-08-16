from z3 import *
import json

# Map each city to an integer
# 0: Oslo, 1: Helsinki, 2: Edinburgh, 3: Riga, 4: Tallinn,
# 5: Budapest, 6: Vilnius, 7: Porto, 8: Geneva
cities = {
    0: "Oslo",
    1: "Helsinki",
    2: "Edinburgh",
    3: "Riga",
    4: "Tallinn",
    5: "Budapest",
    6: "Vilnius",
    7: "Porto",
    8: "Geneva"
}

# Define required days for each city.
# (Note: The “overlap” on flights will account for the fact that the
# sum of these numbers is 33 but 8 days are double–counted, so 33–8 = 25.)
def req_expr(c):
    return If(c == 0, 2,    # Oslo: 2 days
           If(c == 1, 2,    # Helsinki: 2 days
           If(c == 2, 3,    # Edinburgh: 3 days
           If(c == 3, 2,    # Riga: 2 days
           If(c == 4, 5,    # Tallinn: 5 days (wedding must occur between day 4 and 8)
           If(c == 5, 5,    # Budapest: 5 days
           If(c == 6, 5,    # Vilnius: 5 days
           If(c == 7, 5,    # Porto: 5 days
           4)))))))        # Geneva: 4 days

# List the allowed direct flights.
# For the symmetric pairs, both orders are added.
# For the unidirectional ones we add only the allowed direction.
allowed_flights = [
    # symmetric flights
    (7, 0), (0, 7),                # Porto <-> Oslo
    (2, 5), (5, 2),                # Edinburgh <-> Budapest
    (2, 8), (8, 2),                # Edinburgh <-> Geneva
    (2, 7), (7, 2),                # Edinburgh <-> Porto
    (6, 1), (1, 6),                # Vilnius <-> Helsinki
    (3, 0), (0, 3),                # Riga <-> Oslo
    (8, 0), (0, 8),                # Geneva <-> Oslo
    (2, 0), (0, 2),                # Edinburgh <-> Oslo
    (2, 1), (1, 2),                # Edinburgh <-> Helsinki
    (6, 0), (0, 6),                # Vilnius <-> Oslo
    (3, 1), (1, 3),                # Riga <-> Helsinki
    (5, 8), (8, 5),                # Budapest <-> Geneva
    (1, 5), (5, 1),                # Helsinki <-> Budapest
    (1, 0), (0, 1),                # Helsinki <-> Oslo
    (2, 3), (3, 2),                # Edinburgh <-> Riga
    (4, 1), (1, 4),                # Tallinn <-> Helsinki
    (8, 7), (7, 8),                # Geneva <-> Porto
    (5, 0), (0, 5),                # Budapest <-> Oslo
    (1, 8), (8, 1),                # Helsinki <-> Geneva
    (4, 0), (0, 4),                # Tallinn <-> Oslo
    # unidirectional flights:
    (3, 4),                       # Riga -> Tallinn
    (4, 6),                       # Tallinn -> Vilnius
    (3, 6)                        # Riga -> Vilnius
]

# We'll have 9 segments (one per city visited in order)
num_segments = 9
city_vars = [Int(f"city_{i}") for i in range(num_segments)]
start_vars = [Int(f"start_{i}") for i in range(num_segments)]
end_vars = [Int(f"end_{i}") for i in range(num_segments)]

solver = Solver()

# Domain constraints: each city variable must be one of 0..8.
for i in range(num_segments):
    solver.add(And(city_vars[i] >= 0, city_vars[i] <= 8))

# Each segment’s start and end must be within day 1 and day 25.
for i in range(num_segments):
    solver.add(start_vars[i] >= 1, end_vars[i] <= 25)

# The itinerary runs from day 1 to day 25.
solver.add(start_vars[0] == 1)
solver.add(end_vars[num_segments - 1] == 25)

# Each segment’s duration must equal the required number of days for that city.
for i in range(num_segments):
    solver.add(end_vars[i] == start_vars[i] + req_expr(city_vars[i]) - 1)

# Flight overlap: if segment i ends on day X then segment i+1 starts on day X.
for i in range(1, num_segments):
    solver.add(start_vars[i] == end_vars[i-1])

# We must visit all nine cities exactly once.
solver.add(Distinct(city_vars))

# For every flight (i.e. consecutive segments), there must be a direct flight.
for i in range(num_segments - 1):
    flight_possible = []
    for (src, dst) in allowed_flights:
        flight_possible.append(And(city_vars[i] == src, city_vars[i+1] == dst))
    solver.add(Or(flight_possible))

# Friend meeting in Oslo: if visiting Oslo then one of the days in that segment must be day 24 or day 25.
for i in range(num_segments):
    solver.add(Implies(city_vars[i] == 0,
                         Or(And(start_vars[i] <= 24, 24 <= end_vars[i]),
                            And(start_vars[i] <= 25, 25 <= end_vars[i]))))

# Wedding in Tallinn: if visiting Tallinn then the visit must include a day between 4 and 8.
for i in range(num_segments):
    solver.add(Implies(city_vars[i] == 4,
                         And(start_vars[i] <= 8, end_vars[i] >= 4)))

# Solve for a valid itinerary.
if solver.check() == sat:
    model = solver.model()
    itinerary_segments = []
    for i in range(num_segments):
        city_id = model[city_vars[i]].as_long()
        city_name = cities[city_id]
        start_day = model[start_vars[i]].as_long()
        end_day = model[end_vars[i]].as_long()
        # Build the list of days for this segment.
        days = list(range(start_day, end_day + 1))
        itinerary_segments.append({"city": city_name, "days": days})
    output = {"itinerary": itinerary_segments}
    print(json.dumps(output, indent=4))
else:
    print("No solution found")