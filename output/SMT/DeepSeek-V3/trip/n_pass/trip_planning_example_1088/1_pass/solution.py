import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Oslo', 'Stuttgart', 'Reykjavik', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    city_vars = {city: city for city in cities}  # symbolic reference
    
    # Direct flights: each pair is bidirectional
    direct_flights = [
        ('Reykjavik', 'Stuttgart'),
        ('Reykjavik', 'Stockholm'),
        ('Reykjavik', 'Tallinn'),
        ('Stockholm', 'Oslo'),
        ('Stuttgart', 'Porto'),
        ('Oslo', 'Split'),
        ('Stockholm', 'Stuttgart'),
        ('Reykjavik', 'Oslo'),
        ('Oslo', 'Geneva'),
        ('Stockholm', 'Split'),
        ('Reykjavik', 'Stockholm'),
        ('Split', 'Stuttgart'),
        ('Tallinn', 'Oslo'),
        ('Stockholm', 'Geneva'),
        ('Oslo', 'Porto'),
        ('Geneva', 'Porto'),
        ('Geneva', 'Split')
    ]
    
    # Make flight connections bidirectional and ensure no duplicates
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    flight_connections = {city: set() for city in cities}
    for a, b in flight_pairs:
        flight_connections[a].add(b)
        flight_connections[b].add(a)
    
    # Create Z3 variables for each day (1..21)
    days = 21
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    city_to_num = {city: idx for idx, city in enumerate(cities)}
    num_to_city = {idx: city for idx, city in enumerate(cities)}
    
    s = Solver()
    
    # Each day variable must be between 0 and 7 (representing the 8 cities)
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints:
    # Days 1 and 2 in Reykjavik (index 2)
    s.add(day_city[0] == city_to_num['Reykjavik'])
    s.add(day_city[1] == city_to_num['Reykjavik'])
    
    # Porto between days 19-21 (indices 18..20)
    porto_num = city_to_num['Porto']
    s.add(day_city[18] == porto_num)
    s.add(day_city[19] == porto_num)
    s.add(day_city[20] == porto_num)
    
    # Friend in Stockholm between day 2 and day 4 (indices 1..3, at least one day)
    stockholm_num = city_to_num['Stockholm']
    s.add(Or(day_city[1] == stockholm_num, day_city[2] == stockholm_num, day_city[3] == stockholm_num))
    
    # Flight transitions: adjacent days must be same city or connected by direct flight
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either same city or connected
        same_city = current_city == next_city
        connected_cities = []
        for a in flight_connections:
            for b in flight_connections[a]:
                connected_cities.append(And(current_city == city_to_num[a], next_city == city_to_num[b]))
        s.add(Or(same_city, Or(connected_cities)))
    
    # Duration constraints:
    # Count days per city
    counts = {city: 0 for city in cities}
    for city in cities:
        count = 0
        for day in day_city:
            count += If(day == city_to_num[city], 1, 0)
        counts[city] = count
    
    s.add(counts['Oslo'] == 5)
    s.add(counts['Stuttgart'] == 5)
    s.add(counts['Reykjavik'] == 2)  # days 1-2
    s.add(counts['Split'] == 3)
    s.add(counts['Geneva'] == 2)
    s.add(counts['Porto'] == 3)
    s.add(counts['Tallinn'] == 5)
    s.add(counts['Stockholm'] == 3)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_num = model.evaluate(day_city[i]).as_long()
            city = num_to_city[city_num]
            itinerary.append({"day": day_num, "place": city})
        
        # Prepare output
        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))