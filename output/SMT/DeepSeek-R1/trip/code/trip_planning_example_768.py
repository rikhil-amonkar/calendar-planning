from z3 import *

# Define the cities
City = Datatype('City')
City.declare('Mykonos')
City.declare('Nice')
City.declare('London')
City.declare('Copenhagen')
City.declare('Tallinn')
City.declare('Oslo')
City = City.create()

# Define direct flights (bidirectional)
flight_pairs = [
    ('London', 'Copenhagen'),
    ('Copenhagen', 'Tallinn'),
    ('Tallinn', 'Oslo'),
    ('Mykonos', 'London'),
    ('Oslo', 'Nice'),
    ('London', 'Nice'),
    ('Mykonos', 'Nice'),
    ('London', 'Oslo'),
    ('Copenhagen', 'Nice'),
    ('Copenhagen', 'Oslo'),
]

flights = []
for a, b in flight_pairs:
    flights.append((getattr(City, a), getattr(City, b)))
    flights.append((getattr(City, b), getattr(City, a)))

# Create solver
s = Solver()

# City variables for each day (0-based for 16 days)
days = 16
city = [Const(f'city_{i}', City) for i in range(days)]

# Fixed days constraints: day 14 (index 13) and day 16 (index 15) must be Nice
s.add(city[13] == City.Nice)
s.add(city[15] == City.Nice)

# Oslo must be visited between day 10 and 14 (indexes 9 to 13 inclusive)
s.add(Or([city[i] == City.Oslo for i in range(9, 14)]))

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i+1]
    s.add(Or(
        current == next_day,  # Stay in same city
        Or([And(current == a, next_day == b) for (a, b) in flights])  # Take direct flight
    ))

# Total days calculation including arrivals/departures
def total_days(c):
    days_in = Sum([If(city[i] == c, 1, 0) for i in range(days)])
    arrivals = Sum([If(And(city[i] != c, city[i+1] == c), 1, 0) for i in range(days-1)])
    departures = Sum([If(And(city[i] == c, city[i+1] != c), 1, 0) for i in range(days-1)])
    return days_in + arrivals + departures

# Add duration constraints for each city
s.add(total_days(City.Mykonos) == 4)
s.add(total_days(City.Nice) == 3)
s.add(total_days(City.London) == 2)
s.add(total_days(City.Copenhagen) == 3)
s.add(total_days(City.Tallinn) == 4)
s.add(total_days(City.Oslo) == 5)

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")