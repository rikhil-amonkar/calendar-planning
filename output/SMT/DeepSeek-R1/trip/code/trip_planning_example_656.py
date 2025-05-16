from z3 import *

# Define cities
City = Datatype('City')
City.declare('Reykjavik')
City.declare('Istanbul')
City.declare('Edinburgh')
City.declare('Oslo')
City.declare('Stuttgart')
City.declare('Bucharest')
City = City.create()

# Define direct flights (including one-way)
flight_pairs = [
    ('Bucharest', 'Oslo'), ('Oslo', 'Bucharest'),
    ('Istanbul', 'Oslo'), ('Oslo', 'Istanbul'),
    ('Bucharest', 'Istanbul'), ('Istanbul', 'Bucharest'),
    ('Stuttgart', 'Edinburgh'), ('Edinburgh', 'Stuttgart'),
    ('Istanbul', 'Edinburgh'), ('Edinburgh', 'Istanbul'),
    ('Oslo', 'Reykjavik'), ('Reykjavik', 'Oslo'),
    ('Istanbul', 'Stuttgart'), ('Stuttgart', 'Istanbul'),
    ('Oslo', 'Edinburgh'), ('Edinburgh', 'Oslo'),
    ('Reykjavik', 'Stuttgart'),  # One-way
]

flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))

# Create solver
s = Solver()

# City variables for 19 days (0-based)
days = 19
city = [Const(f'city_{i}', City) for i in range(days)]

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i+1]
    s.add(Or(
        current == next_day,
        Or([And(current == a, next_day == b) for (a, b) in flights])
    ))

# Total days calculation considering flights
def total_days(c):
    total = 0
    # Day 0
    total += If(city[0] == c, 1, 0)
    for i in range(1, days):
        prev = city[i-1]
        curr = city[i]
        # If previous and current are the same, add 1 if current is c
        # Else, add 1 if prev is c, and 1 if curr is c
        total += If(prev == curr,
                    If(curr == c, 1, 0),
                    If(prev == c, 1, 0) + If(curr == c, 1, 0))
    return total

# Total days constraints
s.add(total_days(City.Reykjavik) == 5)
s.add(total_days(City.Istanbul) == 4)
s.add(total_days(City.Edinburgh) == 5)
s.add(total_days(City.Oslo) == 2)
s.add(total_days(City.Stuttgart) == 3)
s.add(total_days(City.Bucharest) == 5)

# Istanbul must be visited between day 5-8 (0-based 4-7)
for i in range(days):
    s.add(Implies(city[i] == City.Istanbul, And(i >=4, i <=7)))

# Oslo must be visited between day 8-9 (0-based 7-8)
for i in range(days):
    s.add(Implies(city[i] == City.Oslo, And(i >=7, i <=8)))

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")