import z3
import json

# Define cities and their codes
cities = ['Mykonos', 'Nice', 'London', 'Copenhagen', 'Oslo', 'Tallinn']
city_code = {city: i for i, city in enumerate(cities)}
mykonos = 0
nice = 1
london = 2
copenhagen = 3
oslo = 4
tallinn = 5

# Allowed direct flights as pairs of city codes
allowed_flights = {
    (mykonos, london), (london, mykonos),
    (london, copenhagen), (copenhagen, london),
    (copenhagen, tallinn), (tallinn, copenhagen),
    (tallinn, oslo), (oslo, tallinn),
    (oslo, nice), (nice, oslo),
    (london, nice), (nice, london),
    (mykonos, nice), (nice, mykonos),
    (london, oslo), (oslo, london),
    (copenhagen, nice), (nice, copenhagen),
    (copenhagen, oslo), (oslo, copenhagen),
}

# Create Z3 solver and variables for each day (days 1 to 16, indexes 0 to 15)
solver = z3.Solver()
city_day = [z3.Int(f'day_{i}') for i in range(16)]

# Each city_day must be a valid city code (0-5)
for i in range(16):
    solver.add(z3.And(city_day[i] >= 0, city_day[i] <= 5))

# Transition constraints: if consecutive days differ, the pair must be in allowed_flights
for i in range(15):  # i from 0 to 14 (days 1-15 and 2-16)
    cond = city_day[i] != city_day[i+1]
    allowed_pairs = [z3.And(city_day[i] == a, city_day[i+1] == b) for (a, b) in allowed_flights]
    allowed = z3.Or(allowed_pairs)
    solver.add(z3.Implies(cond, allowed))

# Required days in each city
required_days = [4, 3, 2, 3, 5, 4]  # Mykonos, Nice, London, Copenhagen, Oslo, Tallinn

for city in range(6):
    total = 0
    for x in range(16):
        current = z3.If(city_day[x] == city, 1, 0)
        if x < 15:
            flight_in = z3.If(z3.And(city_day[x] != city_day[x+1], city_day[x+1] == city), 1, 0)
        else:
            flight_in = 0
        total += current + flight_in
    solver.add(total == required_days[city])

# Conference days in Nice (day 14 and 16, indexes 13 and 15)
solver.add(city_day[13] == nice)
solver.add(city_day[15] == nice)

# Oslo meeting between day 10 and 14 (indexes 9 to 13)
oslo_meeting = []
for x in range(9, 14):  # x is 9, 10, 11, 12, 13
    present = z3.Or(
        city_day[x] == oslo,
        z3.And(x < 15, city_day[x] != city_day[x+1], city_day[x+1] == oslo)
    )
    oslo_meeting.append(present)
solver.add(z3.Or(oslo_meeting))

# Solve and output
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(16):
        day_city_code = model[city_day[i]].as_long()
        day_city = cities[day_city_code]
        itinerary.append({f'day_{i+1}': day_city})  # days are 1-based in output
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found.")