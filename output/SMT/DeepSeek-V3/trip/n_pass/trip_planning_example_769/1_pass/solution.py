from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Porto', 'Amsterdam'),
        ('Munich', 'Amsterdam'),
        ('Reykjavik', 'Amsterdam'),
        ('Munich', 'Porto'),
        ('Prague', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Amsterdam', 'Santorini'),
        ('Prague', 'Amsterdam'),
        ('Prague', 'Munich')
    ]
    
    # Create a adjacency list for direct flights
    adjacency = {city: set() for city in cities}
    for a, b in direct_flights:
        adjacency[a].add(b)
        adjacency[b].add(a)
    
    # Z3 variables: day[i] is the city index for day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(16)]  # days 1-16
    
    s = Solver()
    
    # Each day's city must be a valid city index (0 to 5)
    for day in days:
        s.add(day >= 0, day < 6)
    
    # Transition constraints: consecutive days must be same city or connected by direct flight
    for i in range(15):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in the same city or move to a connected city
        possible_transitions = []
        for city_idx in range(6):
            city = idx_to_city[city_idx]
            connected_cities = adjacency[city]
            for connected_city in connected_cities:
                connected_idx = city_to_idx[connected_city]
                possible_transitions.append(And(current_city == city_idx, next_city == connected_idx))
        possible_transitions.append(current_city == next_city)
        s.add(Or(possible_transitions))
    
    # Duration constraints
    # Count the number of days each city appears in the itinerary
    for city in cities:
        count = Sum([If(days[i] == city_to_idx[city], 1, 0) for i in range(16)])
        if city == 'Porto':
            s.add(count == 5)
        elif city == 'Prague':
            s.add(count == 4)
        elif city == 'Reykjavik':
            s.add(count == 4)
        elif city == 'Santorini':
            s.add(count == 2)
        elif city == 'Amsterdam':
            s.add(count == 2)
        elif city == 'Munich':
            s.add(count == 4)
        elif city == 'Munich':
            s.add(count == 4)
    
    # Fixed events
    # Wedding in Reykjavik between day 4 and day 7 (i.e., days 4,5,6,7: at least one of these days is Reykjavik)
    s.add(Or([days[i] == city_to_idx['Reykjavik'] for i in range(3, 7)]))  # days 4-7 (0-based 3-6)
    
    # Conference in Amsterdam on day 14 and 15 (0-based 13 and 14)
    s.add(days[13] == city_to_idx['Amsterdam'])
    s.add(days[14] == city_to_idx['Amsterdam'])
    
    # Meet friend in Munich between day 7 and day 10 (days 7,8,9,10: at least one of these is Munich)
    s.add(Or([days[i] == city_to_idx['Munich'] for i in range(6, 10)]))  # days 7-10 (0-based 6-9)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'city': idx_to_city[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))