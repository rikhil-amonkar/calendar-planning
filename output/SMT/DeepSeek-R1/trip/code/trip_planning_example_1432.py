from z3 import *

# Define cities
City = Datatype('City')
City.declare('Frankfurt')
City.declare('Salzburg')
City.declare('Athens')
City.declare('Reykjavik')
City.declare('Bucharest')
City.declare('Valencia')
City.declare('Vienna')
City.declare('Amsterdam')
City.declare('Stockholm')
City.declare('Riga')
City = City.create()

# Define direct flights (handle one-way and bidirectional)
flight_pairs = [
    # Bidirectional flights
    ('Valencia', 'Frankfurt'), ('Frankfurt', 'Valencia'),
    ('Vienna', 'Bucharest'), ('Bucharest', 'Vienna'),
    ('Athens', 'Bucharest'), ('Bucharest', 'Athens'),
    ('Riga', 'Frankfurt'), ('Frankfurt', 'Riga'),
    ('Stockholm', 'Athens'), ('Athens', 'Stockholm'),
    ('Amsterdam', 'Bucharest'), ('Bucharest', 'Amsterdam'),
    ('Amsterdam', 'Frankfurt'), ('Frankfurt', 'Amsterdam'),
    ('Stockholm', 'Vienna'), ('Vienna', 'Stockholm'),
    ('Vienna', 'Riga'), ('Riga', 'Vienna'),
    ('Amsterdam', 'Reykjavik'), ('Reykjavik', 'Amsterdam'),
    ('Reykjavik', 'Frankfurt'), ('Frankfurt', 'Reykjavik'),
    ('Stockholm', 'Amsterdam'), ('Amsterdam', 'Stockholm'),
    ('Amsterdam', 'Valencia'), ('Valencia', 'Amsterdam'),
    ('Vienna', 'Frankfurt'), ('Frankfurt', 'Vienna'),
    ('Valencia', 'Bucharest'), ('Bucharest', 'Valencia'),
    ('Bucharest', 'Frankfurt'), ('Frankfurt', 'Bucharest'),
    ('Stockholm', 'Frankfurt'), ('Frankfurt', 'Stockholm'),
    ('Valencia', 'Vienna'), ('Vienna', 'Valencia'),
    ('Frankfurt', 'Salzburg'), ('Salzburg', 'Frankfurt'),
    ('Amsterdam', 'Vienna'), ('Vienna', 'Amsterdam'),
    ('Stockholm', 'Reykjavik'), ('Reykjavik', 'Stockholm'),
    ('Amsterdam', 'Riga'), ('Riga', 'Amsterdam'),
    ('Stockholm', 'Riga'), ('Riga', 'Stockholm'),
    ('Vienna', 'Reykjavik'), ('Reykjavik', 'Vienna'),
    ('Amsterdam', 'Athens'), ('Athens', 'Amsterdam'),
    ('Athens', 'Frankfurt'), ('Frankfurt', 'Athens'),
    ('Vienna', 'Athens'), ('Athens', 'Vienna'),
    ('Riga', 'Bucharest'), ('Bucharest', 'Riga'),
    # One-way flights
    ('Valencia', 'Athens'),  # From Valencia to Athens
    ('Athens', 'Riga'),      # From Athens to Riga
    ('Reykjavik', 'Athens')  # From Reykjavik to Athens
]

flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))

# Create solver
s = Solver()

# City variables for 29 days (0-based)
days = 29
city = [Const(f'city_{i}', City) for i in range(days)]

# Fixed day constraints
s.add(city[4] == City.Valencia)   # Day 5
s.add(city[5] == City.Valencia)   # Day 6
s.add(city[17] == City.Riga)      # Day 18
s.add(city[19] == City.Riga)      # Day 20

# Event attendance constraints
s.add(Or([city[i] == City.Stockholm for i in range(0, 3)]))  # Days 1-3
s.add(Or([city[i] == City.Vienna for i in range(5, 10)]))     # Days 6-10
s.add(Or([city[i] == City.Athens for i in range(13, 18)]))    # Days 14-18

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
s.add(total_days(City.Frankfurt) == 4)
s.add(total_days(City.Salzburg) == 5)
s.add(total_days(City.Athens) == 5)
s.add(total_days(City.Reykjavik) == 5)
s.add(total_days(City.Bucharest) == 3)
s.add(total_days(City.Valencia) == 2)
s.add(total_days(City.Vienna) == 5)
s.add(total_days(City.Amsterdam) == 3)
s.add(total_days(City.Stockholm) == 3)
s.add(total_days(City.Riga) == 3)

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")