from z3 import *

# Define the cities
City = Datatype('City')
City.declare('Lisbon')
City.declare('Dubrovnik')
City.declare('Copenhagen')
City.declare('Prague')
City.declare('Tallinn')
City.declare('Stockholm')
City.declare('Split')
City.declare('Lyon')
City = City.create()

# Flight pairs (bidirectional)
flight_pairs = [
    ('Dubrovnik', 'Stockholm'),
    ('Lisbon', 'Copenhagen'),
    ('Lisbon', 'Lyon'),
    ('Copenhagen', 'Stockholm'),
    ('Copenhagen', 'Split'),
    ('Prague', 'Stockholm'),
    ('Tallinn', 'Stockholm'),
    ('Prague', 'Lyon'),
    ('Lisbon', 'Stockholm'),
    ('Prague', 'Lisbon'),
    ('Stockholm', 'Split'),
    ('Prague', 'Copenhagen'),
    ('Split', 'Lyon'),
    ('Copenhagen', 'Dubrovnik'),
    ('Prague', 'Split'),
    ('Tallinn', 'Copenhagen'),
    ('Tallinn', 'Prague'),
]

# Convert to Z3 city pairs
flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))
    flights.append((getattr(City, b), getattr(City, a)))

s = Solver()

# City variables for each day (day 1 to 19)
days = 19
city = [Const(f'city_{i}', City) for i in range(days)]

# Fixed day constraints
s.add(city[0] == City.Tallinn)  # Day 1
s.add(city[1] == City.Tallinn)  # Day 2
s.add(city[3] == City.Lisbon)   # Day 4
s.add(city[4] == City.Lisbon)   # Day 5
s.add(city[12] == City.Stockholm)  # Day 13
s.add(city[13] == City.Stockholm)  # Day 14
s.add(city[14] == City.Stockholm)  # Day 15
s.add(city[15] == City.Stockholm)  # Day 16
s.add(city[17] == City.Lyon)    # Day 18
s.add(city[18] == City.Lyon)    # Day 19

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i+1]
    s.add(Implies(current != next_day, Or([And(current == a, next_day == b) for (a, b) in flights])))

# Total days per city constraints
def total_days(c):
    days_in_city = Sum([If(city[i] == c, 1, 0) for i in range(days)])
    arrivals = Sum([If(And(city[i] != c, city[i+1] == c), 1, 0) for i in range(days-1)])
    return days_in_city + arrivals

s.add(total_days(City.Lisbon) == 2)
s.add(total_days(City.Dubrovnik) == 5)
s.add(total_days(City.Copenhagen) == 5)
s.add(total_days(City.Prague) == 3)
s.add(total_days(City.Tallinn) == 2)
s.add(total_days(City.Stockholm) == 4)
s.add(total_days(City.Split) == 3)
s.add(total_days(City.Lyon) == 2)

# Check and print the solution
if s.check() == sat:
    m = s.model()
    schedule = [m.evaluate(city[i]) for i in range(days)]
    for i in range(days):
        day = i + 1
        city_name = schedule[i]
        print(f"Day {day}: {city_name}")
else:
    print("No valid itinerary found")