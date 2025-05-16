from z3 import *

# Define the cities
City = Datatype('City')
City.declare('Naples')
City.declare('Seville')
City.declare('Milan')
City = City.create()

# Define the direct flights (bidirectional)
flights = [
    (City.Milan, City.Seville),
    (City.Seville, City.Milan),
    (City.Naples, City.Milan),
    (City.Milan, City.Naples),
]

# Create the solver
s = Solver()

# Variables for each day's city (0-based)
days = 12
city = [Const(f'city_{i}', City) for i in range(days)]

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i + 1]
    s.add(Or(current == next_day, Or([And(current == a, next_day == b) for a, b in flights])))

# Seville must be visited from day 9 to 12 (0-based 8-11)
for i in [8, 9, 10, 11]:
    s.add(city[i] == City.Seville)

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
s.add(total_days(City.Naples) == 3)
s.add(total_days(City.Seville) == 4)
s.add(total_days(City.Milan) == 7)

# Check for a solution and print it
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")