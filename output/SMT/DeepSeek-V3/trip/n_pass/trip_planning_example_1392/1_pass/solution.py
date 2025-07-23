import json
from z3 import *

# Define the cities
cities = {
    'Naples': 3,
    'Valencia': 5,
    'Stuttgart': 2,
    'Split': 5,
    'Venice': 5,
    'Amsterdam': 4,
    'Nice': 2,
    'Barcelona': 2,
    'Porto': 4
}

# Direct flights as a set of tuples
direct_flights = {
    ('Venice', 'Nice'),
    ('Naples', 'Amsterdam'),
    ('Barcelona', 'Nice'),
    ('Amsterdam', 'Nice'),
    ('Stuttgart', 'Valencia'),
    ('Stuttgart', 'Porto'),
    ('Split', 'Stuttgart'),
    ('Split', 'Naples'),
    ('Valencia', 'Amsterdam'),
    ('Barcelona', 'Porto'),
    ('Valencia', 'Naples'),
    ('Venice', 'Amsterdam'),
    ('Barcelona', 'Naples'),
    ('Barcelona', 'Valencia'),
    ('Split', 'Amsterdam'),
    ('Barcelona', 'Venice'),
    ('Stuttgart', 'Amsterdam'),
    ('Naples', 'Nice'),
    ('Venice', 'Stuttgart'),
    ('Split', 'Barcelona'),
    ('Porto', 'Nice'),
    ('Barcelona', 'Stuttgart'),
    ('Venice', 'Naples'),
    ('Porto', 'Amsterdam'),
    ('Porto', 'Valencia'),
    ('Stuttgart', 'Naples'),
    ('Barcelona', 'Amsterdam')
}

# Correcting city names in direct_flights to match the keys in 'cities'
corrected_flights = set()
for flight in direct_flights:
    city1, city2 = flight
    # Correct typos in city names
    city1_corrected = city1.replace('Naples', 'Naples').replace('Porto', 'Porto').replace('Barcelona', 'Barcelona').replace('Valencia', 'Valencia').replace('Stuttgart', 'Stuttgart').replace('Split', 'Split').replace('Venice', 'Venice').replace('Amsterdam', 'Amsterdam').replace('Nice', 'Nice')
    city2_corrected = city2.replace('Naples', 'Naples').replace('Porto', 'Porto').replace('Barcelona', 'Barcelona').replace('Valencia', 'Valencia').replace('Stuttgart', 'Stuttgart').replace('Split', 'Split').replace('Venice', 'Venice').replace('Amsterdam', 'Amsterdam').replace('Nice', 'Nice')
    corrected_flights.add((city1_corrected, city2_corrected))
    corrected_flights.add((city2_corrected, city1_corrected))  # flights are bidirectional

direct_flights_set = corrected_flights

# Create a Z3 solver
s = Solver()

# Variables: day_1 to day_24, each can be one of the cities
days = [Int(f'day_{i}') for i in range(1, 25)]
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Each day variable must be one of the city IDs
for day in days:
    s.add(Or([day == city_ids[city] for city in cities]))

# Constraints for total days in each city
for city, total_days in cities.items():
    s.add(Sum([If(day == city_ids[city], 1, 0) for day in days]) == total_days)

# Flight constraints: consecutive days must be either same city or have a direct flight
for i in range(24):
    if i == 23:
        break  # no day after 24
    current_day = days[i]
    next_day = days[i+1]
    # Either stay in the same city or move to a city with a direct flight
    s.add(Or(
        current_day == next_day,
        *[And(current_day == city_ids[city1], next_day == city_ids[city2]) for (city1, city2) in direct_flights_set if city1 in city_ids and city2 in city_ids]
    ))

# Specific constraints:
# 1. Spend 3 days in Naples, with one day between 18 and 20
naples_days = [If(days[i] == city_ids['Naples'], 1, 0) for i in range(17, 20)]  # days 18,19,20 (0-based: 17,18,19)
s.add(Sum(naples_days) >= 1)

# 2. Conference in Venice between day 6 and 10 (inclusive)
for i in range(5, 10):  # days 6-10 (0-based: 5-9)
    s.add(days[i] == city_ids['Venice'])

# 3. Workshop in Barcelona between day 5 and 6
s.add(Or(days[4] == city_ids['Barcelona'], days[5] == city_ids['Barcelona']))  # days 5 and 6 (0-based: 4,5)

# 4. Meet friends in Nice between day 23 and 24
s.add(Or(days[22] == city_ids['Nice'], days[23] == city_ids['Nice']))  # days 23,24 (0-based: 22,23)

# 5. Meet friend in Naples between day 18 and 20
# Already handled in the Naples days constraint above.

# Solve the model
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(24):
        day_num = i + 1
        city_id = model.evaluate(days[i]).as_long()
        city = id_to_city[city_id]
        itinerary.append({'day': day_num, 'place': city})
    
    # Verify the solution meets all constraints
    # (Debugging checks can be added here if needed)
    
    # Output as JSON
    output = {'itinerary': itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")