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

# Create 25 variables: c0 (start of day1) and c1 to c24 (end of days 1 to 24)
c = [Const('c_%d' % i, City) for i in range(25)]

s = Solver()

# Travel constraints: for each day i (from 1 to 24), if moving, must be via direct flight
for i in range(1, 25):
    s.add(If(c[i-1] != c[i], Or([And(c[i-1] == u, c[i] == v) for (u, v) in allowed_pairs]), True))

# Fixed event constraints
# Munich: days 4,5,6
s.add(Or(c[3] == City.Munich, c[4] == City.Munich))  # Day 4
s.add(Or(c[4] == City.Munich, c[5] == City.Munich))  # Day 5
s.add(Or(c[5] == City.Munich, c[6] == City.Munich))  # Day 6
s.add(And(c[5] == City.Munich, c[6] == City.Munich))  # Full day on day 6

# Santorini: days 8,9,10
s.add(Or(c[7] == City.Santorini, c[8] == City.Santorini))  # Day 8
s.add(Or(c[8] == City.Santorini, c[9] == City.Santorini))  # Day 9
s.add(Or(c[9] == City.Santorini, c[10] == City.Santorini))  # Day 10
s.add(And(c[9] == City.Santorini, c[10] == City.Santorini))  # Full day on day 10

# Valencia: days 14,15
s.add(Or(c[13] == City.Valencia, c[14] == City.Valencia))  # Day 14
s.add(Or(c[14] == City.Valencia, c[15] == City.Valencia))  # Day 15
s.add(And(c[14] == City.Valencia, c[15] == City.Valencia))  # Full day on day 15

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
    for day in range(1, 25):  # Days 1 to 24
        total_count += If(Or(c[day-1] == city_const, c[day] == city_const), 1, 0)
    s.add(total_count == total_req)

# Solve and output the schedule
if s.check() == sat:
    m = s.model()
    c_vals = [m.evaluate(c[i]) for i in range(25)]
    for day in range(1, 25):
        start_city = c_vals[day-1]
        end_city = c_vals[day]
        if start_city == end_city:
            cities_today = {start_city}
        else:
            cities_today = {start_city, end_city}
        cities_list = sorted(cities_today, key=lambda x: str(x))
        print(f"Day {day}: {', '.join([str(city) for city in cities_list])}")
else:
    print("No solution found")