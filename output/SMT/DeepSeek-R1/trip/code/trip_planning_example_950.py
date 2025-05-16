from z3 import *

# Define cities
City = Datatype('City')
City.declare('Mykonos')
City.declare('Riga')
City.declare('Munich')
City.declare('Bucharest')
City.declare('Rome')
City.declare('Nice')
City.declare('Krakow')
City = City.create()

# Define direct flights (including one-way)
flight_pairs = [
    # Bidirectional flights
    ('Nice', 'Riga'), ('Riga', 'Nice'),
    ('Bucharest', 'Munich'), ('Munich', 'Bucharest'),
    ('Mykonos', 'Munich'), ('Munich', 'Mykonos'),
    ('Riga', 'Bucharest'), ('Bucharest', 'Riga'),
    ('Rome', 'Nice'), ('Nice', 'Rome'),
    ('Rome', 'Munich'), ('Munich', 'Rome'),
    ('Mykonos', 'Nice'), ('Nice', 'Mykonos'),
    ('Rome', 'Mykonos'), ('Mykonos', 'Rome'),
    ('Munich', 'Krakow'), ('Krakow', 'Munich'),
    ('Rome', 'Bucharest'), ('Bucharest', 'Rome'),
    ('Nice', 'Munich'), ('Munich', 'Nice'),
    # One-way flights
    ('Riga', 'Munich'),  # Riga -> Munich
    ('Rome', 'Riga'),    # Rome -> Riga
]

flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))

# Create solver
s = Solver()

# City variables for 17 days (0-based)
days = 17
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
s.add(total_days(City.Mykonos) == 3)
s.add(total_days(City.Riga) == 3)
s.add(total_days(City.Munich) == 4)
s.add(total_days(City.Bucharest) == 4)
s.add(total_days(City.Rome) == 4)
s.add(total_days(City.Nice) == 3)
s.add(total_days(City.Krakow) == 2)

# Mykonos must be visited between day 4-6 (0-based 3-5)
for i in range(days):
    s.add(Implies(city[i] == City.Mykonos, And(i >= 3, i <= 5)))

# Rome must be visited between day 1-4 (0-based 0-3)
for i in range(days):
    s.add(Implies(city[i] == City.Rome, And(i >= 0, i <= 3)))

# Krakow must be visited between day 16-17 (0-based 15-16)
for i in range(days):
    s.add(Implies(city[i] == City.Krakow, And(i >= 15, i <= 16)))

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")