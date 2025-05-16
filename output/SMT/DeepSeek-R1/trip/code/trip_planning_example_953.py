from z3 import *

# Define the cities
City = Datatype('City')
City.declare('Salzburg')
City.declare('Stockholm')
City.declare('Venice')
City.declare('Frankfurt')
City.declare('Florence')
City.declare('Barcelona')
City.declare('Stuttgart')
City = City.create()

# Define direct flights (bidirectional)
flight_pairs = [
    ('Barcelona', 'Frankfurt'),
    ('Florence', 'Frankfurt'),
    ('Stockholm', 'Barcelona'),
    ('Barcelona', 'Florence'),
    ('Venice', 'Barcelona'),
    ('Stuttgart', 'Barcelona'),
    ('Frankfurt', 'Salzburg'),
    ('Stockholm', 'Frankfurt'),
    ('Stuttgart', 'Stockholm'),
    ('Stuttgart', 'Frankfurt'),
    ('Venice', 'Stuttgart'),
    ('Venice', 'Frankfurt'),
]

flights = []
for a, b in flight_pairs:
    city_a = getattr(City, a)
    city_b = getattr(City, b)
    flights.append((city_a, city_b))
    flights.append((city_b, city_a))

# Create solver
s = Solver()

# Variables for each day's city (0-based)
days = 18
city = [Const(f'city_{i}', City) for i in range(days)]

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i + 1]
    s.add(Or(current == next_day, Or([And(current == a, next_day == b) for a, b in flights])))

# Venice must be visited from day 1 to day 5 (0-based 0-4)
for i in range(5):
    s.add(city[i] == City.Venice)

# Total days function
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

# Add total days constraints
s.add(total_days(City.Salzburg) == 4)
s.add(total_days(City.Stockholm) == 2)
s.add(total_days(City.Venice) == 5)
s.add(total_days(City.Frankfurt) == 4)
s.add(total_days(City.Florence) == 4)
s.add(total_days(City.Barcelona) == 2)
s.add(total_days(City.Stuttgart) == 3)

# Check solution and print
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")