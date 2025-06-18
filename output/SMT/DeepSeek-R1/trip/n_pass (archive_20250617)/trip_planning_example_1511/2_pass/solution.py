from z3 import *

# Define the City datatype
City = Datatype('City')
City.declare('Venice')
City.declare('Reykjavik')
City.declare('Munich')
City.declare('Santorini')
City.declare('Manchester')
City.declare('Porto')
City.declare('Bucharest')
City.declare('Tallinn')
City.declare('Valencia')
City.declare('Vienna')
City = City.create()

# Define direct flights
edges_str = [
    "Bucharest and Manchester",
    "Munich and Venice",
    "Santorini and Manchester",
    "Vienna and Reykjavik",
    "Venice and Santorini",
    "Munich and Porto",
    "Valencia and Vienna",
    "Manchester and Vienna",
    "Porto and Vienna",
    "Venice and Manchester",
    "Santorini and Vienna",
    "Munich and Manchester",
    "Munich and Reykjavik",
    "Bucharest and Valencia",
    "Venice and Vienna",
    "Bucharest and Vienna",
    "Porto and Manchester",
    "Munich and Vienna",
    "Valencia and Porto",
    "Munich and Bucharest",
    "Tallinn and Munich",
    "Santorini and Bucharest",
    "Munich and Valencia"
]

allowed_pairs = []
for s in edges_str:
    u_str, v_str = s.split(' and ')
    u_str = u_str.strip()
    v_str = v_str.strip()
    u_const = getattr(City, u_str)
    v_const = getattr(City, v_str)
    allowed_pairs.append((u_const, v_const))
    allowed_pairs.append((v_const, u_const))

# Create variables for each day: c[0] for day1, c[1] for day2, ..., c[23] for day24
c = [Const('c_%d' % i, City) for i in range(24)]

s = Solver()

# Travel constraints: for consecutive days, if different cities, must be connected by direct flight
for i in range(23):
    s.add(If(c[i] != c[i+1], Or([And(c[i] == u, c[i+1] == v) for (u, v) in allowed_pairs]), True))

# Function to determine if we are in a city on a given day
def in_city(day, city):
    if day == 1:
        return c[0] == city
    else:
        prev_idx = day - 2  # index of the city at the end of the previous day (start of current day)
        curr_idx = day - 1  # index of the city at the end of the current day
        return Or(c[prev_idx] == city, c[curr_idx] == city)

# Fixed event constraints
s.add(in_city(4, City.Munich))
s.add(in_city(5, City.Munich))
s.add(in_city(6, City.Munich))
s.add(in_city(8, City.Santorini))
s.add(in_city(9, City.Santorini))
s.add(in_city(10, City.Santorini))
s.add(in_city(14, City.Valencia))
s.add(in_city(15, City.Valencia))

# Total days per city constraints
city_days = [
    ('Venice', 3),
    ('Reykjavik', 2),
    ('Munich', 3),
    ('Santorini', 3),
    ('Manchester', 3),
    ('Porto', 3),
    ('Bucharest', 5),
    ('Tallinn', 4),
    ('Valencia', 2),
    ('Vienna', 5)
]

for name, total_req in city_days:
    city_const = getattr(City, name)
    total_count = 0
    for day in range(1, 25):
        total_count += If(in_city(day, city_const), 1, 0)
    s.add(total_count == total_req)

# Solve and output the schedule
if s.check() == sat:
    m = s.model()
    c_vals = [m.evaluate(c[i]) for i in range(24)]
    for day in range(1, 25):
        if day == 1:
            cities_today = {c_vals[0]}
        else:
            prev_city = c_vals[day-2]
            curr_city = c_vals[day-1]
            if prev_city == curr_city:
                cities_today = {curr_city}
            else:
                cities_today = {prev_city, curr_city}
        cities_list = sorted(cities_today, key=lambda x: str(x))
        print(f"Day {day}: {', '.join([str(city) for city in cities_list])}")
else:
    print("No solution found")