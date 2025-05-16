from z3 import *

# Define the cities
City = Datatype('City')
City.declare('Split')
City.declare('Helsinki')
City.declare('Reykjavik')
City.declare('Vilnius')
City.declare('Geneva')
City = City.create()

# Define direct flights (bidirectional)
flights = [
    (City.Split, City.Helsinki),
    (City.Helsinki, City.Split),
    (City.Geneva, City.Split),
    (City.Split, City.Geneva),
    (City.Geneva, City.Helsinki),
    (City.Helsinki, City.Geneva),
    (City.Helsinki, City.Reykjavik),
    (City.Reykjavik, City.Helsinki),
    (City.Vilnius, City.Helsinki),
    (City.Helsinki, City.Vilnius),
    (City.Split, City.Vilnius),
    (City.Vilnius, City.Split),
]

# Create solver
s = Solver()

# Variables for each day's city (0-based)
days = 12
city = [Const(f'city_{i}', City) for i in range(days)]

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i + 1]
    s.add(Or(current == next_day, Or([And(current == a, next_day == b) for a, b in flights])))

# Reykjavik must be visited from day 10 to 12 (0-based 9-11)
for i in [9, 10, 11]:
    s.add(city[i] == City.Reykjavik)

# Vilnius must be visited between day 7-9 (0-based 6-8)
for i in [6, 7, 8]:
    s.add(city[i] == City.Vilnius)

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
s.add(total_days(City.Split) == 2)
s.add(total_days(City.Helsinki) == 2)
s.add(total_days(City.Reykjavik) == 3)
s.add(total_days(City.Vilnius) == 3)
s.add(total_days(City.Geneva) == 6)

# Check solution and print
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")