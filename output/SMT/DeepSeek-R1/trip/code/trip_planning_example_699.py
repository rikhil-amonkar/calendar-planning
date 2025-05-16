from z3 import *

# Define the cities
City = Datatype('City')
City.declare('Mykonos')
City.declare('Reykjavik')
City.declare('Dublin')
City.declare('London')
City.declare('Helsinki')
City.declare('Hamburg')
City = City.create()

# Define direct flights (bidirectional)
flight_pairs = [
    ('Dublin', 'London'),
    ('Hamburg', 'Dublin'),
    ('Helsinki', 'Reykjavik'),
    ('Hamburg', 'London'),
    ('Dublin', 'Helsinki'),
    ('Reykjavik', 'London'),
    ('London', 'Mykonos'),
    ('Dublin', 'Reykjavik'),
    ('Hamburg', 'Helsinki'),
    ('Helsinki', 'London'),
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
days = 16
city = [Const(f'city_{i}', City) for i in range(days)]

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i + 1]
    s.add(Or(current == next_day, Or([And(current == a, next_day == b) for a, b in flights])))

# Specific date constraints
s.add(city[0] == City.Hamburg)  # Meet friends in Hamburg on day 1 (1-based)
for i in [1,2,3,4,5]:  # Attend Dublin show from day 2-6 (1-based)
    s.add(city[i] == City.Dublin)
s.add(city[8] == City.Reykjavik)  # Wedding on day 9 (1-based)
s.add(city[9] == City.Reykjavik)  # Wedding on day 10 (1-based)

# Total days function
def total_days(c):
    total = 0
    total += If(city[0] == c, 1, 0)  # Handle day 0
    for i in range(1, days):
        prev = city[i-1]
        curr = city[i]
        total += If(prev == curr,
                    If(curr == c, 1, 0),
                    If(prev == c, 1, 0) + If(curr == c, 1, 0))
    return total

# Add total days constraints
s.add(total_days(City.Mykonos) == 3)
s.add(total_days(City.Reykjavik) == 2)
s.add(total_days(City.Dublin) == 5)
s.add(total_days(City.London) == 5)
s.add(total_days(City.Helsinki) == 4)
s.add(total_days(City.Hamburg) == 2)

# Check solution and print
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")