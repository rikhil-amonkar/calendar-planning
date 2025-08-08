from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Krakow', 'Split'),
        ('Split', 'Athens'),
        ('Edinburgh', 'Krakow'),
        ('Venice', 'Stuttgart'),
        ('Krakow', 'Stuttgart'),
        ('Edinburgh', 'Stuttgart'),
        ('Stuttgart', 'Athens'),
        ('Venice', 'Edinburgh'),
        ('Athens', 'Mykonos'),
        ('Venice', 'Athens'),
        ('Stuttgart', 'Split'),
        ('Edinburgh', 'Athens')
    ]
    
    # Create adjacency list for flights
    adjacency = {city: set() for city in cities}
    for src, dst in direct_flights:
        adjacency[src].add(dst)
        adjacency[dst].add(src)
    
    # Z3 variables: for each day, which city are we in?
    days = 20
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day's city must be a valid city index (0..6)
    for dc in day_city:
        s.add(And(dc >= 0, dc <= 6))
    
    # Flight constraints: consecutive days must be same city or connected by flight
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_city == next_city)
        possible_flights = []
        for city_idx in range(7):
            city = cities[city_idx]
            for neighbor in adjacency[city]:
                neighbor_idx = city_map[neighbor]
                possible_flights.append(And(current_city == city_idx, next_city == neighbor_idx))
        s.add(Or(same_city, Or(possible_flights)))
    
    # City stay constraints
    # Stuttgart: 3 days total, including workshop days 11-13 (days 10-12 in 0-based)
    stuttgart_idx = city_map['Stuttgart']
    s.add(Sum([If(day_city[i] == stuttgart_idx, 1, 0) for i in range(days)]) == 3)
    # At least one of days 11,12,13 must be in Stuttgart (1-based: days 10,11,12 in 0-based)
    s.add(Or(day_city[10] == stuttgart_idx, day_city[11] == stuttgart_idx, day_city[12] == stuttgart_idx))
    
    # Edinburgh: 4 days
    edinburgh_idx = city_map['Edinburgh']
    s.add(Sum([If(day_city[i] == edinburgh_idx, 1, 0) for i in range(days)]) == 4)
    
    # Athens: 4 days
    athens_idx = city_map['Athens']
    s.add(Sum([If(day_city[i] == athens_idx, 1, 0) for i in range(days)]) == 4)
    
    # Split: 2 days, and meet friends between day 13-14 (0-based 12-13)
    split_idx = city_map['Split']
    s.add(Sum([If(day_city[i] == split_idx, 1, 0) for i in range(days)]) == 2)
    s.add(Or(day_city[12] == split_idx, day_city[13] == split_idx))
    
    # Krakow: 4 days, meet friend between day 8-11 (0-based 7-10)
    krakow_idx = city_map['Krakow']
    s.add(Sum([If(day_city[i] == krakow_idx, 1, 0) for i in range(days)]) == 4)
    s.add(Or([day_city[i] == krakow_idx for i in range(7, 11)]))
    
    # Venice: 5 days
    venice_idx = city_map['Venice']
    s.add(Sum([If(day_city[i] == venice_idx, 1, 0) for i in range(days)]) == 5)
    
    # Mykonos: 4 days
    mykonos_idx = city_map['Mykonos']
    s.add(Sum([If(day_city[i] == mykonos_idx, 1, 0) for i in range(days)]) == 4)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_city[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return result
    else:
        return {"error": "No valid itinerary found"}

# Run the solver
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))