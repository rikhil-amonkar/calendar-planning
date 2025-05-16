from z3 import *

City = Datatype('City')
City.declare('Prague')
City.declare('Tallinn')
City.declare('Warsaw')
City.declare('Porto')
City.declare('Naples')
City.declare('Milan')
City.declare('Lisbon')
City.declare('Santorini')
City.declare('Riga')
City.declare('Stockholm')
City = City.create()

flight_entries = [
    "Riga and Prague",
    "Stockholm and Milan",
    "Riga and Milan",
    "Lisbon and Stockholm",
    "from Stockholm to Santorini",
    "Naples and Warsaw",
    "Lisbon and Warsaw",
    "Naples and Milan",
    "Lisbon and Naples",
    "from Riga to Tallinn",
    "Tallinn and Prague",
    "Stockholm and Warsaw",
    "Riga and Warsaw",
    "Lisbon and Riga",
    "Riga and Stockholm",
    "Lisbon and Porto",
    "Lisbon and Prague",
    "Milan and Porto",
    "Prague and Milan",
    "Lisbon and Milan",
    "Warsaw and Porto",
    "Warsaw and Tallinn",
    "Santorini and Milan",
    "Stockholm and Prague",
    "Stockholm and Tallinn",
    "Warsaw and Milan",
    "Santorini and Naples",
    "Warsaw and Prague",
]

flights = []
for entry in flight_entries:
    if entry.startswith("from "):
        parts = entry.split()
        a, b = parts[1], parts[3]
        city_a = getattr(City, a)
        city_b = getattr(City, b)
        flights.append((city_a, city_b))
    else:
        a, b = entry.split(" and ")
        city_a = getattr(City, a)
        city_b = getattr(City, b)
        flights.append((city_a, city_b))
        flights.append((city_b, city_a))

days = 28
s = Solver()
city = [Const(f'city_{i}', City) for i in range(days)]

for i in range(days - 1):
    current, next_day = city[i], city[i+1]
    s.add(Or(current == next_day, Or([And(current == a, next_day == b) for (a, b) in flights])))

s.add(city[4] == City.Riga)
s.add(city[5] == City.Riga)
s.add(city[6] == City.Riga)
s.add(city[7] == City.Riga)
s.add(city[17] == City.Tallinn)
s.add(city[18] == City.Tallinn)
s.add(city[19] == City.Tallinn)
s.add(city[23] == City.Milan)
s.add(city[24] == City.Milan)
s.add(city[25] == City.Milan)

def total_days(c):
    total = If(city[0] == c, 1, 0)
    for i in range(1, days):
        prev, curr = city[i-1], city[i]
        total += If(prev == curr, If(curr == c, 1, 0), If(prev == c, 1, 0) + If(curr == c, 1, 0))
    return total

s.add(total_days(City.Prague) == 5)
s.add(total_days(City.Tallinn) == 3)
s.add(total_days(City.Warsaw) == 2)
s.add(total_days(City.Porto) == 3)
s.add(total_days(City.Naples) == 5)
s.add(total_days(City.Milan) == 3)
s.add(total_days(City.Lisbon) == 5)
s.add(total_days(City.Santorini) == 5)
s.add(total_days(City.Riga) == 4)
s.add(total_days(City.Stockholm) == 2)

if s.check() == sat:
    m = s.model()
    schedule = [(i+1, m.evaluate(city[i])) for i in range(days)]
    for day, city_val in schedule:
        print(f"Day {day}: {city_val}")
else:
    print("No valid itinerary found")