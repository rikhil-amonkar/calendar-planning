from z3 import *

# Define the cities
cities = ['Salzburg', 'Hamburg', 'Venice', 'Nice', 'Zurich', 'Bucharest', 'Copenhagen', 'Brussels', 'Naples', 'Barcelona']
City, city_consts = EnumSort('City', cities)
salzburg, hamburg, venice, nice, zurich, bucharest, copenhagen, brussels, naples, barcelona = city_consts

# Direct flights (both directions)
direct_flights = [
    (salzburg, hamburg), (salzburg, venice), (salzburg, nice), (salzburg, zurich),
    (hamburg, salzburg), (hamburg, venice), (hamburg, nice), (hamburg, zurich), (hamburg, bucharest), (hamburg, copenhagen), (hamburg, brussels), (hamburg, naples), (hamburg, barcelona),
    (venice, salzburg), (venice, hamburg), (venice, nice), (venice, zurich), (venice, bucharest), (venice, naples), (venice, barcelona),
    (nice, salzburg), (nice, hamburg), (nice, venice), (nice, zurich), (nice, brussels), (nice, barcelona),
    (zurich, salzburg), (zurich, hamburg), (zurich, venice), (zurich, nice), (zurich, bucharest), (zurich, copenhagen), (zurich, brussels), (zurich, naples), (zurich, barcelona),
    (bucharest, hamburg), (bucharest, venice), (bucharest, zurich), (bucharest, copenhagen), (bucharest, brussels), (bucharest, naples), (bucharest, barcelona),
    (copenhagen, hamburg), (copenhagen, zurich), (copenhagen, bucharest), (copenhagen, brussels), (copenhagen, naples), (copenhagen, barcelona),
    (brussels, hamburg), (brussels, nice), (brussels, zurich), (brussels, bucharest), (brussels, copenhagen), (brussels, naples), (brussels, barcelona),
    (naples, hamburg), (naples, venice), (naples, zurich), (naples, bucharest), (naples, copenhagen), (naples, brussels), (naples, barcelona),
    (barcelona, hamburg), (barcelona, venice), (barcelona, nice), (barcelona, zurich), (barcelona, bucharest), (barcelona, copenhagen), (barcelona, brussels), (barcelona, naples)
]

# Create solver
s = Solver()

# City for each day (1 to 25)
city_day = [ Const(f'city_day_{i}', City) for i in range(1, 26) ]

# Constraint: Each day is one of the cities
for i in range(25):
    s.add(Or([city_day[i] == c for c in city_consts]))

# Start and end constraints
s.add(city_day[0] == salzburg)
s.add(city_day[24] == naples)

# Flight constraints
for i in range(24):
    current = city_day[i]
    next_day = city_day[i+1]
    same_city = (current == next_day)
    flight_exists = Or([ And(current == src, next_day == dst) for (src, dst) in direct_flights ])
    s.add(Or(same_city, flight_exists))

# Each city must appear at least once
for c in city_consts:
    s.add(Or([city_day[i] == c for i in range(25)]))

# Prevent leaving a city and returning later (ensures contiguous blocks)
for c in city_consts:
    for i in range(0, 24):  # From day 0 to 23 (0-indexed)
        for j in range(i+2, 25):  # From day i+2 to 24 (0-indexed)
            s.add(Not(And(
                city_day[i] == c, 
                city_day[i+1] != c,
                city_day[j] == c
            )))

# Check and get model
if s.check() == sat:
    m = s.model()
    # Get the string representation of the city for each day
    city_strings = [str(m.evaluate(city_day[i], model_completion=True)) for i in range(25)]
    
    # Build itinerary by grouping consecutive days with same city
    itinerary = []
    current_city = city_strings[0]
    start_day = 1
    for i in range(1, 25):
        if city_strings[i] != current_city:
            end_day = i
            itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': current_city})
            current_city = city_strings[i]
            start_day = i+1
    itinerary.append({'day_range': f'Day {start_day}-25', 'place': current_city})
    print(f"Plan found: {{'itinerary': {itinerary}}}")
else:
    print("No valid plan found.")