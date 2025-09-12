from z3 import *
import json

# Define cities and their durations
cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
durations = {
    'Valencia': 2,
    'Oslo': 3,
    'Lyon': 4,
    'Prague': 3,
    'Paris': 4,
    'Nice': 4,
    'Seville': 5,
    'Tallinn': 2,
    'Mykonos': 5,
    'Lisbon': 2
}

# Create EnumSort for cities
City = Datatype('City')
for city in cities:
    City.declare(city)
City = City.create()

# Define direct flights (bidirectional)
direct_flights = [
    ('Lisbon', 'Paris'),
    ('Lyon', 'Nice'),
    ('Tallinn', 'Oslo'),
    ('Prague', 'Lyon'),
    ('Paris', 'Oslo'),
    ('Lisbon', 'Seville'),
    ('Prague', 'Lisbon'),
    ('Oslo', 'Nice'),
    ('Valencia', 'Paris'),
    ('Valencia', 'Lisbon'),
    ('Paris', 'Nice'),
    ('Nice', 'Mykonos'),
    ('Paris', 'Lyon'),
    ('Valencia', 'Lyon'),
    ('Prague', 'Oslo'),
    ('Prague', 'Paris'),
    ('Seville', 'Paris'),
    ('Oslo', 'Lyon'),
    ('Prague', 'Valencia'),
    ('Lisbon', 'Nice'),
    ('Lisbon', 'Oslo'),
    ('Valencia', 'Seville'),
    ('Lisbon', 'Lyon'),
    ('Paris', 'Tallinn'),
    ('Prague', 'Tallinn'),
]

# Generate allowed flight pairs as tuples of City EnumSort values
allowed_pairs = []
for a_str, b_str in direct_flights:
    a = getattr(City, a_str)
    b = getattr(City, b_str)
    allowed_pairs.append((a, b))
    allowed_pairs.append((b, a))

# Function to get duration based on city variable
def get_duration(city_var):
    return If(city_var == City.Valencia, 2,
              If(city_var == City.Oslo, 3,
                 If(city_var == City.Lyon, 4,
                    If(city_var == City.Prague, 3,
                       If(city_var == City.Paris, 4,
                          If(city_var == City.Nice, 4,
                             If(city_var == City.Seville, 5,
                                If(city_var == City.Tallinn, 2,
                                   If(city_var == City.Mykonos, 5,
                                      If(city_var == City.Lisbon, 2, 0))))))))

# Create solver
s = Solver()

# Create sequence variables
seq = [Const(f's_{i}', City) for i in range(10)]

# All cities must be distinct
s.add(Distinct(seq))

# Create start_day variables
start_day = [Int(f'd_{i}') for i in range(10)]

# First day starts at 1
s.add(start_day[0] == 1)

# Compute start_day for each city based on previous city's duration
for i in range(1, 10):
    prev_duration = get_duration(seq[i-1])
    s.add(start_day[i] == start_day[i-1] + prev_duration)

# Add event constraints for each city
for i in range(10):
    # Valencia: start_day between 2 and 4
    s.add(Implies(seq[i] == City.Valencia, And(start_day[i] >= 2, start_day[i] <= 4)))
    # Oslo: start_day between 11 and 15
    s.add(Implies(seq[i] == City.Oslo, And(start_day[i] >= 11, start_day[i] <= 15)))
    # Seville: start_day == 5
    s.add(Implies(seq[i] == City.Seville, start_day[i] == 5))
    # Mykonos: start_day == 21
    s.add(Implies(seq[i] == City.Mykonos, start_day[i] == 21))

# Add flight constraints between consecutive cities
for i in range(9):
    constraints = []
    for a, b in allowed_pairs:
        constraints.append(And(seq[i] == a, seq[i+1] == b))
    s.add(Or(constraints))

# Check if the problem is satisfiable
if s.check() == sat:
    m = s.model()
    # Extract the sequence and start_day values
    sequence = [m.evaluate(seq[i]) for i in range(10)]
    start_days = [m.evaluate(start_day[i]) for i in range(10)]
    # Now, create the itinerary
    itinerary = []
    for i in range(10):
        city_name = str(sequence[i])
        duration = durations[city_name]
        end_day = start_days[i] + duration - 1
        day_range = f"Day {start_days[i]}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")