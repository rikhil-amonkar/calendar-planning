from z3 import *
import json

cities = ["Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw", "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"]
durations = {
    "Bucharest": 2,
    "Krakow": 4,
    "Munich": 3,
    "Barcelona": 5,
    "Warsaw": 5,
    "Budapest": 5,
    "Stockholm": 2,
    "Riga": 5,
    "Edinburgh": 5,
    "Vienna": 5,
}

direct_flights = {
    ("Budapest", "Munich"),
    ("Bucharest", "Riga"),
    ("Munich", "Krakow"),
    ("Munich", "Warsaw"),
    ("Munich", "Bucharest"),
    ("Edinburgh", "Stockholm"),
    ("Barcelona", "Warsaw"),
    ("Edinburgh", "Krakow"),
    ("Barcelona", "Munich"),
    ("Stockholm", "Krakow"),
    ("Budapest", "Vienna"),
    ("Barcelona", "Riga"),
    ("Edinburgh", "Munich"),
    ("Barcelona", "Bucharest"),
    ("Edinburgh", "Riga"),
    ("Vienna", "Riga"),
    ("Barcelona", "Budapest"),
    ("Bucharest", "Warsaw"),
    ("Vienna", "Bucharest"),
    ("Budapest", "Warsaw"),
    ("Vienna", "Warsaw"),
    ("Barcelona", "Vienna"),
    ("Budapest", "Bucharest"),
    ("Vienna", "Munich"),
    ("Riga", "Warsaw"),
    ("Stockholm", "Riga"),
    ("Stockholm", "Warsaw"),
}

direct_flight_pairs = []
for c1, c2 in direct_flights:
    direct_flight_pairs.append((c1, c2))
    direct_flight_pairs.append((c2, c1))

seq = [String(f"city_{i}") for i in range(10)]
s = Solver()

# All cities must be in the sequence and distinct
for i in range(10):
    s.add(Or([seq[i] == city for city in cities]))
s.add(Distinct(seq))

# Direct flight between consecutive cities
for i in range(9):
    city1 = seq[i]
    city2 = seq[i+1]
    constraints = []
    for c1, c2 in direct_flight_pairs:
        constraints.append(And(city1 == c1, city2 == c2))
    s.add(Or(constraints))

# Define start and end days
start_days = [Int(f"start_{i}") for i in range(10)]
end_days = [Int(f"end_{i}") for i in range(10)]

# First city starts on day 1
s.add(start_days[0] == 1)

# end_day[i] = start_day[i] + duration - 1
for i in range(10):
    city = seq[i]
    dur = durations[city]
    s.add(end_days[i] == start_days[i] + dur - 1)

# start_day[i+1] = end_day[i] + 1
for i in range(9):
    s.add(start_days[i+1] == end_days[i] + 1)

# Add specific constraints

# Workshop in Munich between day 18-20: start_day >=16 and <=20
for i in range(10):
    s.add(Implies(seq[i] == "Munich", And(start_days[i] >= 16, start_days[i] <= 20)))

# Conference in Warsaw on day 25 and 29: start_day ==25
for i in range(10):
    s.add(Implies(seq[i] == "Warsaw", start_days[i] == 25))

# Annual show in Budapest from day 9-13: start_day ==9
for i in range(10):
    s.add(Implies(seq[i] == "Budapest", start_days[i] == 9))

# Meeting friends in Stockholm between day 17-18: start_day >=16 and <=18
for i in range(10):
    s.add(Implies(seq[i] == "Stockholm", And(start_days[i] >= 16, start_days[i] <= 18)))

# Meeting a friend in Edinburgh between day 1-5: start_day <=5
for i in range(10):
    s.add(Implies(seq[i] == "Edinburgh", start_days[i] <= 5))

# Check if the solver can find a solution
if s.check() == sat:
    m = s.model()
    sequence = [m.evaluate(seq[i]).as_string() for i in range(10)]
    start_days_values = [m.evaluate(start_days[i]).as_long() for i in range(10)]
    end_days_values = [m.evaluate(end_days[i]).as_long() for i in range(10)]
    
    # Build the itinerary
    itinerary = []
    for i in range(10):
        city = sequence[i]
        start = start_days_values[i]
        end = end_days_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")