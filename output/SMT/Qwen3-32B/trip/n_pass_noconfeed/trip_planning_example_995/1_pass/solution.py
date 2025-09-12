from z3 import *

# Define cities as an EnumSort
City, (Barcelona, Brussels, Copenhagen, Oslo, Split, Stuttgart, Venice) = EnumSort('City', ['Barcelona', 'Brussels', 'Copenhagen', 'Oslo', 'Split', 'Stuttgart', 'Venice'])

# Create variables for the cities in order
c = [Const(f'c_{i}', City) for i in range(7)]

# Solver instance
s = Solver()

# All cities must be distinct
s.add(Distinct(c))

# First city must be Barcelona
s.add(c[0] == Barcelona)

# Allowed flights (bidirectional)
allowed_flights = [
    (Venice, Stuttgart), (Stuttgart, Venice),
    (Oslo, Brussels), (Brussels, Oslo),
    (Split, Copenhagen), (Copenhagen, Split),
    (Barcelona, Copenhagen), (Copenhagen, Barcelona),
    (Barcelona, Venice), (Venice, Barcelona),
    (Brussels, Venice), (Venice, Brussels),
    (Barcelona, Stuttgart), (Stuttgart, Barcelona),
    (Copenhagen, Brussels), (Brussels, Copenhagen),
    (Oslo, Split), (Split, Oslo),
    (Oslo, Venice), (Venice, Oslo),
    (Barcelona, Split), (Split, Barcelona),
    (Oslo, Copenhagen), (Copenhagen, Oslo),
    (Barcelona, Oslo), (Oslo, Barcelona),
    (Copenhagen, Stuttgart), (Stuttgart, Copenhagen),
    (Split, Stuttgart), (Stuttgart, Split),
    (Copenhagen, Venice), (Venice, Copenhagen),
    (Barcelona, Brussels), (Brussels, Barcelona),
]

# Add constraints for consecutive cities to have direct flights
for i in range(6):
    constraints = []
    for a, b in allowed_flights:
        constraints.append(And(c[i] == a, c[i+1] == b))
    s.add(Or(constraints))

# Create start_day variables
start_days = [Int(f'start_day_{i}') for i in range(7)]

# Add constraint for the first day
s.add(start_days[0] == 1)

# For each city in the order, compute duration and add constraints
for i in range(7):
    duration = If(c[i] == Barcelona, 3,
            If(c[i] == Brussels, 3,
            If(c[i] == Copenhagen, 3,
            If(c[i] == Oslo, 2,
            If(c[i] == Split, 4,
            If(c[i] == Stuttgart, 3, 4)))))  # Venice has 4
    end_day = start_days[i] + duration - 1
    if i < 6:
        s.add(start_days[i+1] == end_day)

# Add constraints for Oslo's start_day
for i in range(7):
    s.add(Implies(c[i] == Oslo, start_days[i] == 3))

# Add constraints for Brussels' start_day between 7 and 11
for i in range(7):
    s.add(Implies(c[i] == Brussels, And(start_days[i] >= 7, start_days[i] <= 11)))

# Check for solution
if s.check() == sat:
    m = s.model()
    # Extract the cities order
    cities_order = [m.evaluate(c[i]) for i in range(7)]
    # Extract start_days
    start_days_values = [m.evaluate(start_days[i]).as_long() for i in range(7)]
    # Compute end_days
    end_days_values = []
    for i in range(7):
        city = str(cities_order[i])
        duration = 0
        if city == 'Barcelona':
            duration = 3
        elif city == 'Brussels':
            duration = 3
        elif city == 'Copenhagen':
            duration = 3
        elif city == 'Oslo':
            duration = 2
        elif city == 'Split':
            duration = 4
        elif city == 'Stuttgart':
            duration = 3
        elif city == 'Venice':
            duration = 4
        end_day = start_days_values[i] + duration - 1
        end_days_values.append(end_day)
    
    # Build the itinerary
    itinerary = []
    for i in range(7):
        start = start_days_values[i]
        end = end_days_values[i]
        city_name = str(cities_order[i])
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")