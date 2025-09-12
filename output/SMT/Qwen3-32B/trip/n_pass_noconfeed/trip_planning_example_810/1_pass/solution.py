import json
from z3 import *

# Define the cities
Cities, cities = EnumSort('Cities', ['Berlin', 'Barcelona', 'Lyon', 'Nice', 'Athens', 'Stockholm', 'Vilnius'])

# Create itinerary variables
itin = [Const(f'itin_{i}', Cities) for i in range(7)]

# Solver
s = Solver()

# Fix first three cities
s.add(itin[0] == cities.Berlin)
s.add(itin[1] == cities.Barcelona)
s.add(itin[2] == cities.Lyon)

# The remaining cities (positions 3-6) must be a permutation of Nice, Athens, Stockholm, Vilnius
remaining_cities = [cities.Nice, cities.Athens, cities.Stockholm, cities.Vilnius]

# Add constraints that positions 3-6 are all in remaining_cities and distinct
for i in range(3, 7):
    s.add(Or([itin[i] == city for city in remaining_cities]))

s.add(Distinct(itin[3], itin[4], itin[5], itin[6]))

# Allowed direct flights (both directions)
allowed_flights = [
    (cities.Berlin, cities.Barcelona),
    (cities.Barcelona, cities.Berlin),
    (cities.Berlin, cities.Nice),
    (cities.Nice, cities.Berlin),
    (cities.Berlin, cities.Vilnius),
    (cities.Vilnius, cities.Berlin),
    (cities.Berlin, cities.Stockholm),
    (cities.Stockholm, cities.Berlin),
    (cities.Barcelona, cities.Nice),
    (cities.Nice, cities.Barcelona),
    (cities.Barcelona, cities.Lyon),
    (cities.Lyon, cities.Barcelona),
    (cities.Barcelona, cities.Athens),
    (cities.Athens, cities.Barcelona),
    (cities.Barcelona, cities.Stockholm),
    (cities.Stockholm, cities.Barcelona),
    (cities.Lyon, cities.Nice),
    (cities.Nice, cities.Lyon),
    (cities.Nice, cities.Athens),
    (cities.Athens, cities.Nice),
    (cities.Nice, cities.Stockholm),
    (cities.Stockholm, cities.Nice),
    (cities.Athens, cities.Vilnius),
    (cities.Vilnius, cities.Athens),
    (cities.Stockholm, cities.Athens),
    (cities.Athens, cities.Stockholm),
]

# Add constraints for transitions between consecutive cities
for i in range(6):  # i from 0 to 6-1=6
    current = itin[i]
    next_city = itin[i+1]
    # The transition (current, next_city) must be in allowed_flights
    constraints = []
    for (a, b) in allowed_flights:
        constraints.append(And(current == a, next_city == b))
    s.add(Or(constraints))

# Check if the solver can find a model
if s.check() == sat:
    model = s.model()
    # Extract the itinerary sequence
    itinerary = [model.evaluate(itin[i]) for i in range(7)]
    # Now compute the day ranges
    durations = {
        cities.Berlin: 3,
        cities.Barcelona: 2,
        cities.Lyon: 2,
        cities.Nice: 5,
        cities.Athens: 5,
        cities.Stockholm: 5,
        cities.Vilnius: 4,
    }
    result = []
    start_day = 1
    for city in itinerary:
        dur = durations[city]
        end_day = start_day + dur - 1
        # Append to result
        result.append({
            'day_range': f"Day {start_day}-{end_day}",
            'place': city.name
        })
        start_day = end_day  # Next city starts on this day

    output = {"itinerary": result}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")