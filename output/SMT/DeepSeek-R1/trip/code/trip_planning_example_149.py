from z3 import *

# Define the cities
City = Datatype('City')
City.declare('London')
City.declare('Santorini')
City.declare('Istanbul')
City = City.create()

# Define direct flights (bidirectional)
flights = [
    (City.Istanbul, City.London),
    (City.London, City.Istanbul),
    (City.London, City.Santorini),
    (City.Santorini, City.London),
]

# Create solver
s = Solver()

# City variables for each day (0-based for 10 days)
days = 10
city = [Const(f'city_{i}', City) for i in range(days)]

# Fixed days constraints: day 5 (index 4) and day 10 (index 9) must be Santorini
s.add(city[4] == City.Santorini)
s.add(city[9] == City.Santorini)

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

# Add duration constraints
s.add(total_days(City.London) == 3)
s.add(total_days(City.Santorini) == 6)
s.add(total_days(City.Istanbul) == 3)

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city in schedule:
        print(f"Day {day}: {city}")
else:
    print("No valid itinerary found")