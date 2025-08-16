from z3 import *

# Define the cities as an EnumSort
Cities, (Dubrovnik, Split, Milan, Porto, Krakow, Munich) = EnumSort('Cities', ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich'])

# Create the sequence variables for the cities
cities = [Const('C%s' % i, Cities) for i in range(6)]

# All cities must be distinct
distinct = Distinct(cities)

# Define allowed direct flights
allowed_flights = {
    (Dubrovnik, Munich), (Munich, Dubrovnik),
    (Munich, Porto), (Porto, Munich),
    (Split, Milan), (Milan, Split),
    (Milan, Porto), (Porto, Milan),
    (Munich, Krakow), (Krakow, Munich),
    (Munich, Milan), (Milan, Munich),
    (Krakow, Split), (Split, Krakow),
    (Krakow, Milan), (Milan, Krakow),
    (Munich, Split), (Split, Munich),
}

# Constraints for consecutive cities to have direct flights
flight_constraints = []
for i in range(5):
    prev_city = cities[i]
    next_city = cities[i + 1]
    constraints = []
    for (a, b) in allowed_flights:
        constraints.append(And(prev_city == a, next_city == b))
    flight_constraints.append(Or(constraints))

# Start day variables for each city in the sequence
S = [Int('S%s' % i) for i in range(6)]

# Start day constraints
start_day_constraints = [S[0] == 1]
for i in range(1, 6):
    prev_city = cities[i - 1]
    duration_prev = If(prev_city == Dubrovnik, 4,
                       If(prev_city == Split, 3,
                          If(prev_city == Milan, 3,
                             If(prev_city == Porto, 4,
                                If(prev_city == Krakow, 2,
                                   If(prev_city == Munich, 5, 0))))))
    start_day_constraints.append(S[i] == S[i - 1] + duration_prev - 1)

# Event constraints
event_constraints = []
for i in range(6):
    city = cities[i]
    s_i = S[i]
    event_constraints.append(Implies(city == Munich, s_i == 4))
    event_constraints.append(Implies(city == Milan, And(s_i >= 9, s_i <= 13)))
    event_constraints.append(Implies(city == Krakow, And(s_i >= 7, s_i <= 9)))

# Combine all constraints
all_constraints = [distinct] + flight_constraints + start_day_constraints + event_constraints

# Create solver and add constraints
solver = Solver()
solver.add(all_constraints)

# Check if satisfiable
if solver.check() == sat:
    model = solver.model()
    city_sequence = [model.evaluate(c) for c in cities]
    start_days = [model.evaluate(s).as_long() for s in S]
    city_names = {
        Dubrovnik: 'Dubrovnik',
        Split: 'Split',
        Milan: 'Milan',
        Porto: 'Porto',
        Krakow: 'Krakow',
        Munich: 'Munich'
    }

    # Generate the itinerary
    day_city = []
    for i in range(6):
        city = city_sequence[i]
        start = start_days[i]
        duration = 0
        if city == Dubrovnik:
            duration = 4
        elif city == Split:
            duration = 3
        elif city == Milan:
            duration = 3
        elif city == Porto:
            duration = 4
        elif city == Krakow:
            duration = 2
        elif city == Munich:
            duration = 5
        for day in range(start, start + duration):
            day_city.append((day, city))

    # Sort by day and prepare JSON output
    day_city.sort()
    json_itinerary = [{"day": day, "city": city_names[city]} for day, city in day_city]
    print(json.dumps({"itinerary": json_itinerary}, indent=2))
else:
    print("No solution found.")