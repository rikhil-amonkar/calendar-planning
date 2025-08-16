from z3 import *
import json

# Define cities and their durations
cities = ["Paris", "Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Stockholm"]
city_ids = {name: idx for idx, name in enumerate(cities)}
durations = {
    0: 2,  # Paris
    1: 4,  # Vienna
    2: 2,  # Barcelona
    3: 4,  # Edinburgh
    4: 3,  # Krakow
    5: 4,  # Riga
    6: 2,  # Hamburg
    7: 2,  # Stockholm
}

# Define direct flights (bidirectional)
direct_flights = set()
pairs = [
    (6,7), (7,6),
    (1,7), (7,1),
    (0,3), (3,0),
    (5,2), (2,5),
    (0,5), (5,0),
    (4,2), (2,4),
    (3,7), (7,3),
    (0,4), (4,0),
    (4,7), (7,4),
    (5,3), (3,5),
    (2,7), (7,2),
    (0,7), (7,0),
    (4,3), (3,4),
    (1,6), (6,1),
    (0,6), (6,0),
    (5,7), (7,5),
    (6,2), (2,6),
    (1,2), (2,1),
    (4,1), (1,4),
    (5,6), (6,5),
    (2,3), (3,2),
    (0,2), (2,0),
    (6,3), (3,6),
    (0,1), (1,0),
    (1,5), (5,1),
]
direct_flights.update(pairs)

# Create Z3 solver
s = Solver()

# Define sequence of cities
sequence = [Int('seq_{}'.format(i)) for i in range(8)]
s.add(Distinct(sequence))
s.add(sequence[0] == 0)  # First city is Paris

# Define start and end days for each position
start_days = [Int('start_day_{}'.format(i)) for i in range(8)]
end_days = [Int('end_day_{}'.format(i)) for i in range(8)]

# Function to get duration based on city ID
def get_duration(city):
    return If(city == 0, 2,
              If(city == 1, 4,
                 If(city == 2, 2,
                    If(city == 3, 4,
                       If(city == 4, 3,
                          If(city == 5, 4,
                             If(city == 6, 2, 2))))))

# Constraints for duration
for i in range(8):
    duration_i = get_duration(sequence[i])
    s.add(end_days[i] == start_days[i] + duration_i - 1)

# Constraints for fixed start_days
for i in range(8):
    s.add(Implies(sequence[i] == 6, start_days[i] == 10))  # Hamburg
    s.add(Implies(sequence[i] == 3, start_days[i] == 12))  # Edinburgh
    s.add(Implies(sequence[i] == 7, start_days[i] == 15))  # Stockholm

# Constraints for consecutive transitions
for i in range(7):
    s.add(end_days[i] == start_days[i+1])
    allowed_pairs = []
    for a, b in direct_flights:
        allowed_pairs.append(And(sequence[i] == a, sequence[i+1] == b))
    s.add(Or(allowed_pairs))

# Ensure the last end_day is 16
s.add(end_days[7] == 16)

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    # Extract the sequence
    seq_values = [m.evaluate(sequence[i]).as_long() for i in range(8)]
    itinerary_seq = [cities[val] for val in seq_values]
    # Extract start_days and end_days
    start_day_values = [m.evaluate(start_days[i]).as_long() for i in range(8)]
    end_day_values = [m.evaluate(end_days[i]).as_long() for i in range(8)]
    # Build the itinerary
    itinerary = []
    for i in range(8):
        city = itinerary_seq[i]
        start = start_day_values[i]
        end = end_day_values[i]
        for day in range(start, end + 1):
            itinerary.append({f"Day {day}": city})
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")