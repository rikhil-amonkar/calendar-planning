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
    parts = s.split(' and ')
    if len(parts) < 2:
        continue
    u_str = parts[0].strip()
    v_str = parts[1].strip()
    u_const = getattr(City, u_str, None)
    v_const = getattr(City, v_str, None)
    if u_const is not None and v_const is not None:
        allowed_pairs.append((u_const, v_const))
        allowed_pairs.append((v_const, u_const))

# Remove any duplicates
allowed_pairs = list(set(allowed_pairs))

# Create variables: start (before day1) and c0 to c23 (end of days 1 to 24)
start = Const('start', City)
c = [Const(f'c_{i}', City) for i in range(24)]  # c0: end of day1, c1: end of day2, ..., c23: end of day24

s = Solver()

# Travel constraints for day1: from start to c0
s.add(Or(start == c[0], Or([And(start == u, c[0] == v) for (u, v) in allowed_pairs])))

# Travel constraints for subsequent days
for i in range(23):
    s.add(Or(c[i] == c[i+1], Or([And(c[i] == u, c[i+1] == v) for (u, v) in allowed_pairs])))

# Function to check if a city is visited on a given day
def in_city(day, city):
    if day == 1:
        return Or(start == city, c[0] == city)
    else:
        return Or(c[day-2] == city, c[day-1] == city)

# Fixed event constraints
# Munich: days 4,5,6
s.add(in_city(4, City.Munich))
s.add(in_city(5, City.Munich))
s.add(in_city(6, City.Munich))
# Full day on day6: start and end must be Munich
s.add(c[5] == City.Munich)  # End of day6 is Munich
s.add(Or(c[4] == City.Munich, c[5] == City.Munich))  # Start of day6 is Munich (end of day5) or end of day6

# Santorini: days 8,9,10
s.add(in_city(8, City.Santorini))
s.add(in_city(9, City.Santorini))
s.add(in_city(10, City.Santorini))
# Full day on day10
s.add(c[9] == City.Santorini)  # End of day10
s.add(Or(c[8] == City.Santorini, c[9] == City.Santorini))  # Start of day10 (end of day9) or end of day10

# Valencia: days 14,15
s.add(in_city(14, City.Valencia))
s.add(in_city(15, City.Valencia))
# Full day on day15
s.add(c[14] == City.Valencia)  # End of day15
s.add(Or(c[13] == City.Valencia, c[14] == City.Valencia))  # Start of day15 (end of day14) or end of day15

# Total days per city
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
    start_val = m.evaluate(start)
    c_vals = [m.evaluate(c_i) for c_i in c]
    
    # Output each day
    for day in range(1, 25):
        if day == 1:
            # Day1: from start to c0
            city_start = start_val
            city_end = c_vals[0]
        else:
            city_start = c_vals[day-2]
            city_end = c_vals[day-1]
        
        if city_start == city_end:
            cities_today = {city_start}
        else:
            cities_today = {city_start, city_end}
        
        # Sort cities alphabetically for consistent output
        cities_sorted = sorted(cities_today, key=lambda x: str(x))
        print(f"Day {day}: {', '.join([str(city) for city in cities_sorted])}")
else:
    print("No solution found")