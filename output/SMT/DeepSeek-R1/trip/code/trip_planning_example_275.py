from z3 import *

# Define cities
City = Datatype('City')
City.declare('Split')
City.declare('Vilnius')
City.declare('Santorini')
City.declare('Madrid')
City = City.create()

# Define direct flights (bidirectional)
flight_pairs = [
    ('Vilnius', 'Split'),
    ('Split', 'Vilnius'),
    ('Split', 'Madrid'),
    ('Madrid', 'Split'),
    ('Madrid', 'Santorini'),
    ('Santorini', 'Madrid'),
]

flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))

# Create solver
s = Solver()

# City variables for 14 days (0-based)
days = 14
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
s.add(total_days(City.Split) == 5)
s.add(total_days(City.Vilnius) == 4)
s.add(total_days(City.Santorini) == 2)
s.add(total_days(City.Madrid) == 6)

# Santorini must be on days 13-14 (0-based 12-13)
s.add(city[12] == City.Santorini)
s.add(city[13] == City.Santorini)

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")