from z3 import *

# Define cities
City = Datatype('City')
City.declare('Oslo')
City.declare('Helsinki')
City.declare('Edinburgh')
City.declare('Riga')
City.declare('Tallinn')
City.declare('Budapest')
City.declare('Vilnius')
City.declare('Porto')
City.declare('Geneva')
City = City.create()

# Define direct flights (including one-way)
flight_pairs = [
    # Bidirectional flights
    ('Porto', 'Oslo'), ('Oslo', 'Porto'),
    ('Edinburgh', 'Budapest'), ('Budapest', 'Edinburgh'),
    ('Edinburgh', 'Geneva'), ('Geneva', 'Edinburgh'),
    ('Edinburgh', 'Porto'), ('Porto', 'Edinburgh'),
    ('Vilnius', 'Helsinki'), ('Helsinki', 'Vilnius'),
    ('Riga', 'Oslo'), ('Oslo', 'Riga'),
    ('Geneva', 'Oslo'), ('Oslo', 'Geneva'),
    ('Edinburgh', 'Oslo'), ('Oslo', 'Edinburgh'),
    ('Edinburgh', 'Helsinki'), ('Helsinki', 'Edinburgh'),
    ('Vilnius', 'Oslo'), ('Oslo', 'Vilnius'),
    ('Riga', 'Helsinki'), ('Helsinki', 'Riga'),
    ('Budapest', 'Geneva'), ('Geneva', 'Budapest'),
    ('Helsinki', 'Budapest'), ('Budapest', 'Helsinki'),
    ('Helsinki', 'Oslo'), ('Oslo', 'Helsinki'),
    ('Edinburgh', 'Riga'), ('Riga', 'Edinburgh'),
    ('Tallinn', 'Helsinki'), ('Helsinki', 'Tallinn'),
    ('Geneva', 'Porto'), ('Porto', 'Geneva'),
    ('Budapest', 'Oslo'), ('Oslo', 'Budapest'),
    ('Helsinki', 'Geneva'), ('Geneva', 'Helsinki'),
    ('Tallinn', 'Oslo'), ('Oslo', 'Tallinn'),
    # One-way flights
    ('Riga', 'Tallinn'),
    ('Tallinn', 'Vilnius'),
    ('Riga', 'Vilnius'),
]

flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))

# Create solver
s = Solver()

# City variables for 25 days (0-based)
days = 25
city = [Const(f'city_{i}', City) for i in range(days)]

# Fixed day constraints
s.add(city[23] == City.Oslo)  # Day 24
s.add(city[24] == City.Oslo)  # Day 25
s.add(And([city[i] == City.Tallinn for i in range(3, 8)]))  # Days 4-8 (0-based 3-7)

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i+1]
    s.add(Or(
        current == next_day,
        Or([And(current == a, next_day == b) for (a, b) in flights])
    ))

# Total days calculation including arrivals/departures
def total_days(c):
    days_in = Sum([If(city[i] == c, 1, 0) for i in range(days)])
    arrivals = Sum([If(And(city[i] != c, city[i+1] == c), 1, 0) for i in range(days-1)])
    departures = Sum([If(And(city[i] == c, city[i+1] != c), 1, 0) for i in range(days-1)])
    return days_in + arrivals + departures

# Add total days constraints
s.add(total_days(City.Oslo) == 2)
s.add(total_days(City.Helsinki) == 2)
s.add(total_days(City.Edinburgh) == 3)
s.add(total_days(City.Riga) == 2)
s.add(total_days(City.Tallinn) == 5)
s.add(total_days(City.Budapest) == 5)
s.add(total_days(City.Vilnius) == 5)
s.add(total_days(City.Porto) == 5)
s.add(total_days(City.Geneva) == 4)

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")