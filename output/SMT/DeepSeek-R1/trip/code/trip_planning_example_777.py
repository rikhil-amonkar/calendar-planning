from z3 import *

# Define cities
City = Datatype('City')
City.declare('Dublin')
City.declare('Helsinki')
City.declare('Riga')
City.declare('Reykjavik')
City.declare('Vienna')
City.declare('Tallinn')
City = City.create()

# Direct flights (including unidirectional where mentioned)
flight_pairs = [
    # Bidirectional flights
    ('Helsinki', 'Riga'),
    ('Riga', 'Helsinki'),
    ('Vienna', 'Helsinki'),
    ('Helsinki', 'Vienna'),
    ('Riga', 'Dublin'),
    ('Dublin', 'Riga'),
    ('Vienna', 'Riga'),
    ('Riga', 'Vienna'),
    ('Reykjavik', 'Vienna'),
    ('Vienna', 'Reykjavik'),
    ('Helsinki', 'Dublin'),
    ('Dublin', 'Helsinki'),
    ('Tallinn', 'Dublin'),
    ('Dublin', 'Tallinn'),
    ('Reykjavik', 'Helsinki'),
    ('Helsinki', 'Reykjavik'),
    ('Reykjavik', 'Dublin'),
    ('Dublin', 'Reykjavik'),
    ('Helsinki', 'Tallinn'),
    ('Tallinn', 'Helsinki'),
    ('Vienna', 'Dublin'),
    ('Dublin', 'Vienna'),
    # Unidirectional flight
    ('Riga', 'Tallinn'),
]

flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))

# Create solver
s = Solver()

# City variables for 15 days (0-based)
days = 15
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
        total += If(prev == curr,
                    If(curr == c, 1, 0),
                    If(prev == c, 1, 0) + If(curr == c, 1, 0))
    return total

# Total days constraints
s.add(total_days(City.Dublin) == 5)
s.add(total_days(City.Helsinki) == 3)
s.add(total_days(City.Riga) == 3)
s.add(total_days(City.Reykjavik) == 2)
s.add(total_days(City.Vienna) == 2)
s.add(total_days(City.Tallinn) == 5)

# Helsinki must be visited between day 3 and 5 (1-based days 3-5 → 0-based days 2-4)
for i in [2, 3, 4]:
    s.add(city[i] == City.Helsinki)

# Vienna must be visited between day 2 and 3 (1-based days 2-3 → 0-based days 1-2)
s.add(city[1] == City.Vienna)
s.add(city[2] == City.Vienna)

# Tallinn must be visited between day 7 and 11 (1-based days 7-11 → 0-based days 6-10)
for i in range(6, 11):
    s.add(city[i] == City.Tallinn)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")