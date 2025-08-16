from z3 import *
import json

# Define cities and their required days
cities = ["Hamburg", "Munich", "Split", "Lyon", "Manchester"]
required_days = {
    "Hamburg": 7,
    "Munich": 6,
    "Split": 7,
    "Lyon": 2,
    "Manchester": 2
}

# Map cities to integers
city_to_int = {city: i for i, city in enumerate(cities)}
int_to_city = {i: city for i, city in enumerate(cities)}

# Create Z3 variables for the sequence of cities
seq = [Int(f"seq_{i}") for i in range(5)]

# Solver
s = Solver()

# Each city appears exactly once
s.add(Distinct(seq))
for i in range(5):
    s.add(And(seq[i] >= 0, seq[i] < 5))

# Define start and end days for each city in the sequence
start_day = [Int(f"start_day_{i}") for i in range(5)]
end_day = [Int(f"end_day_{i}") for i in range(5)]

# Constraints for start and end days
for i in range(5):
    s.add(start_day[i] >= 1)
    # Determine required_days based on seq[i]
    rd = If(seq[i] == 0, 7,
            If(seq[i] == 1, 6,
               If(seq[i] == 2, 7,
                  If(seq[i] == 3, 2, 2))))
    s.add(end_day[i] == start_day[i] + rd - 1)

# The start day of the next city is the end day of the previous
for i in range(4):
    s.add(start_day[i+1] == end_day[i])

# The total end day is 20
s.add(end_day[4] == 20)

# Constraints for events:
# Lyon must have start_day 13 and end_day 14
lyon_idx = city_to_int["Lyon"]
manchester_idx = city_to_int["Manchester"]

# For all i in 0-4, if seq[i] is Lyon, then start_day[i] == 13 and end_day[i] == 14
for i in range(5):
    s.add(If(seq[i] == lyon_idx, And(start_day[i] == 13, end_day[i] == 14), True))

# For all i in 0-4, if seq[i] is Manchester, then start_day[i] == 19 and end_day[i] == 20
for i in range(5):
    s.add(If(seq[i] == manchester_idx, And(start_day[i] == 19, end_day[i] == 20), True))

# Allowed transitions
allowed_transitions = [
    ("Hamburg", "Munich"),
    ("Munich", "Hamburg"),
    ("Hamburg", "Manchester"),
    ("Manchester", "Hamburg"),
    ("Hamburg", "Split"),
    ("Split", "Hamburg"),
    ("Munich", "Split"),
    ("Split", "Munich"),
    ("Munich", "Manchester"),
    ("Manchester", "Munich"),
    ("Munich", "Lyon"),
    ("Lyon", "Munich"),
    ("Split", "Lyon"),
    ("Lyon", "Split"),
    ("Manchester", "Split"),
    ("Split", "Manchester"),
]

# Add constraints for allowed transitions between consecutive cities
for i in range(4):
    constraints = []
    for c1, c2 in allowed_transitions:
        constraints.append(And(seq[i] == city_to_int[c1], seq[i+1] == city_to_int[c2]))
    s.add(Or(constraints))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    # Extract the sequence
    seq_values = [model.evaluate(seq[i]) for i in range(5)]
    sequence = [int_to_city[seq_values[i]] for i in range(5)]
    # Extract start and end days
    start_days = [model.evaluate(start_day[i]).as_long() for i in range(5)]
    end_days = [model.evaluate(end_day[i]).as_long() for i in range(5)]

    # Build the itinerary
    itinerary = []
    for i in range(5):
        city = sequence[i]
        sd = start_days[i]
        ed = end_days[i]
        for day in range(sd, ed + 1):
            itinerary.append({"day": day, "city": city})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: x["day"])

    # Print the JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")