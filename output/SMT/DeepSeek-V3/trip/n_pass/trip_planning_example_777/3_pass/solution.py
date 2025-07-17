from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    city_map = {city: idx for idx, city in enumerate(cities)}
    idx_map = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Helsinki', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Helsinki'),
        ('Riga', 'Dublin'),
        ('Vienna', 'Riga'),
        ('Reykjavik', 'Vienna'),
        ('Helsinki', 'Dublin'),
        ('Tallinn', 'Dublin'),
        ('Reykjavik', 'Helsinki'),
        ('Reykjavik', 'Dublin'),
        ('Helsinki', 'Tallinn'),
        ('Vienna', 'Dublin')
    ]
    
    # Create a adjacency list for flight connections
    flight_graph = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Z3 solver
    s = Solver()
    
    # Variables: day 1 to 15, each is a city (represented by an integer 0..5)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Constraints for total days in each city
    total_days = [
        ('Dublin', 5),
        ('Helsinki', 3),
        ('Riga', 3),
        ('Reykjavik', 2),
        ('Vienna', 2),
        ('Tallinn', 5)
    ]
    
    for city, required_days in total_days:
        city_idx = city_map[city]
        s.add(Sum([If(day == city_idx, 1, 0) for day in days]) == required_days)
    
    # Specific constraints:
    # Vienna: annual show between day 2 and day 3. So must be in Vienna on day 2 or 3.
    vienna_idx = city_map['Vienna']
    s.add(Or(days[1] == vienna_idx, days[2] == vienna_idx))  # days[1] is day 2, days[2] is day 3
    
    # Helsinki: meet friends between day 3 and day 5 (days 3,4,5: indices 2,3,4)
    helsinki_idx = city_map['Helsinki']
    s.add(Or([days[i] == helsinki_idx for i in [2, 3, 4]]))  # at least one of days 3,4,5
    
    # Tallinn: wedding between day 7 and 11 (days 7-11: indices 6-10)
    tallinn_idx = city_map['Tallinn']
    s.add(Or([days[i] == tallinn_idx for i in range(6, 11)]))
    
    # Flight constraints: adjacent days must be same city or connected by direct flight
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i+1]
        # Either same city or connected
        same_city = current_city == next_city
        connected = Or([And(current_city == city_map[a], next_city == city_map[b]) for a, b in direct_flights] +
                       [And(current_city == city_map[b], next_city == city_map[a]) for a, b in direct_flights])
        s.add(Or(same_city, connected))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 16):
            day_val = model.evaluate(days[i-1])
            city = idx_map[int(str(day_val))]
            itinerary.append({'day': i, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))