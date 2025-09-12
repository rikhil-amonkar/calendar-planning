import z3
import json

# Define cities and their required durations
cities = [
    'Prague',
    'Warsaw',
    'Dublin',
    'Athens',
    'Vilnius',
    'Porto',
    'London',
    'Seville',
    'Lisbon',
    'Dubrovnik'
]
city_to_int = {city: i for i, city in enumerate(cities)}
int_to_city = {i: city for i, city in enumerate(cities)}

required_durations = {
    'Prague': 3,
    'Warsaw': 4,
    'Dublin': 3,
    'Athens': 3,
    'Vilnius': 4,
    'Porto': 5,
    'London': 3,
    'Seville': 2,
    'Lisbon': 5,
    'Dubrovnik': 3
}

# Direct flights (city pairs)
direct_flights = {
    ('Warsaw', 'Vilnius'),
    ('Prague', 'Athens'),
    ('London', 'Lisbon'),
    ('Lisbon', 'Porto'),
    ('Prague', 'Lisbon'),
    ('London', 'Dublin'),
    ('Athens', 'Vilnius'),
    ('Athens', 'Dublin'),
    ('Prague', 'London'),
    ('London', 'Warsaw'),
    ('Dublin', 'Seville'),
    ('Seville', 'Porto'),
    ('Lisbon', 'Athens'),
    ('Dublin', 'Porto'),
    ('Athens', 'Warsaw'),
    ('Lisbon', 'Warsaw'),
    ('Porto', 'Warsaw'),
    ('Prague', 'Warsaw'),
    ('Prague', 'Dublin'),
    ('Athens', 'Dubrovnik'),
    ('Lisbon', 'Dublin'),
    ('Dubrovnik', 'Dublin'),
    ('Lisbon', 'Seville'),
    ('London', 'Athens')
}

# Convert direct flights to integer pairs
allowed_flights = set()
for (a, b) in direct_flights:
    allowed_flights.add((city_to_int[a], city_to_int[b]))
    allowed_flights.add((city_to_int[b], city_to_int[a]))  # Assuming bidirectional flights

# Create solver
s = z3.Solver()

# Create variables for each day (1 to 26)
days = 26
day_vars = [z3.Int(f'day_{i+1}') for i in range(days)]

# Constraints for each day to be one of the cities
for d in day_vars:
    s.add(z3.Or([d == i for i in range(len(cities))]))

# Constraints for consecutive days to have allowed transitions
for i in range(days - 1):
    prev = day_vars[i]
    curr = day_vars[i + 1]
    transitions = []
    for a, b in allowed_flights:
        transitions.append(z3.And(prev == a, curr == b))
    s.add(z3.Or(transitions))

# Constraints for required durations
for city, duration in required_durations.items():
    city_index = city_to_int[city]
    count = sum(z3.If(day_vars[i] == city_index, 1, 0) for i in range(days))
    s.add(count == duration)

# Event constraints
prague_index = city_to_int['Prague']
warsaw_index = city_to_int['Warsaw']
porto_index = city_to_int['Porto']
london_index = city_to_int['London']
lisbon_index = city_to_int['Lisbon']

# Prague workshop between day 1-3 (indices 0,1,2)
s.add(z3.Or(day_vars[0] == prague_index, day_vars[1] == prague_index, day_vars[2] == prague_index))

# Warsaw friends between day 20-23 (indices 19-22)
s.add(z3.Or(day_vars[19] == warsaw_index, day_vars[20] == warsaw_index, day_vars[21] == warsaw_index, day_vars[22] == warsaw_index))

# Porto conference between day 16-20 (indices 15-19)
s.add(z3.Or(day_vars[15] == porto_index, day_vars[16] == porto_index, day_vars[17] == porto_index, day_vars[18] == porto_index, day_vars[19] == porto_index))

# London wedding between day 3-5 (indices 2-4)
s.add(z3.Or(day_vars[2] == london_index, day_vars[3] == london_index, day_vars[4] == london_index))

# Lisbon relatives between day 5-9 (indices 4-8)
s.add(z3.Or(day_vars[4] == lisbon_index, day_vars[5] == lisbon_index, day_vars[6] == lisbon_index, day_vars[7] == lisbon_index, day_vars[8] == lisbon_index))

# Check for solution
if s.check() == z3.sat:
    model = s.model()
    itinerary = []
    current_city = None
    start_day = 1
    for i in range(days):
        day = i + 1  # days are 1-based
        city_idx = model[day_vars[i]].as_long()
        city_name = int_to_city[city_idx]
        if current_city is None:
            current_city = city_name
            start_day = day
        elif city_name != current_city:
            end_day = day - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
            current_city = city_name
            start_day = day
    # Append the last city
    end_day = days
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")