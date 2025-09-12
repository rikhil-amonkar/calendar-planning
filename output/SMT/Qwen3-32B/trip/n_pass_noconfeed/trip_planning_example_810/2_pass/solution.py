import json
from z3 import *

# Define the cities using EnumSort and unpack into individual variables
Cities, (Berlin, Barcelona, Lyon, Nice, Athens, Stockholm, Vilnius) = EnumSort('Cities', [
    'Berlin', 'Barcelona', 'Lyon', 'Nice', 'Athens', 'Stockholm', 'Vilnius'
])

# Create itinerary variables
itin = [Const(f'itin_{i}', Cities) for i in range(7)]

# Solver
s = Solver()

# Fix first three cities
s.add(itin[0] == Berlin)
s.add(itin[1] == Barcelona)
s.add(itin[2] == Lyon)

# The remaining cities (positions 3-6) must be a permutation of Nice, Athens, Stockholm, Vilnius
remaining_cities = [Nice, Athens, Stockholm, Vilnius]

# Add constraints that positions 3-6 are all in remaining_cities and distinct
for i in range(3, 7):
    s.add(Or([itin[i] == city for city in remaining_cities]))

s.add(Distinct(itin[3], itin[4], itin[5], itin[6]))

# Allowed direct flights (both directions)
allowed_flights = [
    (Berlin, Barcelona), (Barcelona, Berlin),
    (Berlin, Nice), (Nice, Berlin),
    (Berlin, Vilnius), (Vilnius, Berlin),
    (Berlin, Stockholm), (Stockholm, Berlin),
    (Barcelona, Nice), (Nice, Barcelona),
    (Barcelona, Lyon), (Lyon, Barcelona),
    (Barcelona, Athens), (Athens, Barcelona),
    (Barcelona, Stockholm), (Stockholm, Barcelona),
    (Lyon, Nice), (Nice, Lyon),
    (Nice, Athens), (Athens, Nice),
    (Nice, Stockholm), (Stockholm, Nice),
    (Athens, Vilnius), (Vilnius, Athens),
    (Stockholm, Athens), (Athens, Stockholm),
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
        Berlin: 3,
        Barcelona: 2,
        Lyon: 2,
        Nice: 5,
        Athens: 5,
        Stockholm: 5,
        Vilnius: 4,
    }
    result = []
    start_day = 1
    for city in itinerary:
        dur = durations[city]
        end_day = start_day + dur - 1
        result.append({
            'day_range': f"Day {start_day}-{end_day}",
            'place': city.name
        })
        start_day = end_day  # Next city starts on this day

    output = {"itinerary": result}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")