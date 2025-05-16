from z3 import *

# Define the cities
City = Datatype('City')
City.declare('Mykonos')
City.declare('Krakow')
City.declare('Vilnius')
City.declare('Helsinki')
City.declare('Dubrovnik')
City.declare('Oslo')
City.declare('Madrid')
City.declare('Paris')
City = City.create()

# Flight pairs (including unidirectional where specified)
flight_list = [
    "Oslo and Krakow",
    "Oslo and Paris",
    "Paris and Madrid",
    "Helsinki and Vilnius",
    "Oslo and Madrid",
    "Oslo and Helsinki",
    "Helsinki and Krakow",
    "Dubrovnik and Helsinki",
    "Dubrovnik and Madrid",
    "Oslo and Dubrovnik",
    "Krakow and Paris",
    "Madrid and Mykonos",
    "Oslo and Vilnius",
    "from Krakow to Vilnius",
    "Helsinki and Paris",
    "Vilnius and Paris",
    "Helsinki and Madrid",
]

flights = []
for entry in flight_list:
    if entry.startswith('from '):
        parts = entry.split(' ')
        a, b = parts[1], parts[3]
        flights.append((getattr(City, a), getattr(City, b)))
    else:
        a, b = entry.split(' and ')
        flights.append((getattr(City, a), getattr(City, b)))
        flights.append((getattr(City, b), getattr(City, a)))

s = Solver()

# City variables for each day (0-based for 18 days)
days = 18
city = [Const(f'city_{i}', City) for i in range(days)]

# Fixed day constraints
s.add(city[0] == City.Oslo)   # Day 1
s.add(city[1] == City.Oslo)   # Day 2
s.add(city[1] == City.Dubrovnik)  # Day 2
s.add(city[2] == City.Dubrovnik)  # Day 3
s.add(city[3] == City.Dubrovnik)  # Day 4
s.add(city[14] == City.Mykonos)  # Day 15
s.add(city[15] == City.Mykonos)  # Day 16
s.add(city[16] == City.Mykonos)  # Day 17
s.add(city[17] == City.Mykonos)  # Day 18

# Flight constraints between consecutive days
for i in range(days - 1):
    current = city[i]
    next_day = city[i+1]
    s.add(Implies(current != next_day, Or([And(current == a, next_day == b) for (a, b) in flights])))

# Total days per city including arrivals and departures
def total_days(c):
    days_in_city = Sum([If(city[i] == c, 1, 0) for i in range(days)])
    arrivals = Sum([If(And(city[i] != c, city[i+1] == c), 1, 0) for i in range(days-1)])
    departures = Sum([If(And(city[i] == c, city[i+1] != c), 1, 0) for i in range(days-1)])
    return days_in_city + arrivals + departures

s.add(total_days(City.Mykonos) == 4)
s.add(total_days(City.Krakow) == 5)
s.add(total_days(City.Vilnius) == 2)
s.add(total_days(City.Helsinki) == 2)
s.add(total_days(City.Dubrovnik) == 3)
s.add(total_days(City.Oslo) == 2)
s.add(total_days(City.Madrid) == 5)
s.add(total_days(City.Paris) == 2)

# Check and print the solution
if s.check() == sat:
    m = s.model()
    schedule = [m.evaluate(city[i]) for i in range(days)]
    for i in range(days):
        print(f"Day {i+1}: {schedule[i]}")
else:
    print("No valid itinerary found")