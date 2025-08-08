from z3 import *

def solve_itinerary():
    # Cities and their required stay durations
    cities = {
        'Reykjavik': 2,
        'Stockholm': 2,
        'Porto': 5,
        'Nice': 3,
        'Venice': 4,
        'Vienna': 3,
        'Split': 3,
        'Copenhagen': 2
    }
    city_list = list(cities.keys())
    city_map = {city: idx for idx, city in enumerate(city_list)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Copenhagen', 'Vienna'),
        ('Nice', 'Stockholm'),
        ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'),
        ('Nice', 'Porto'),
        ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'),
        ('Nice', 'Venice'),
        ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'),
        ('Nice', 'Copenhagen'),
        ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'),
        ('Copenhagen', 'Porto'),
        ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Vienna'),
        ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto')
    ]
    
    # Create flight connections graph
    flight_graph = {city: set() for city in city_list}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Z3 solver
    s = Solver()
    
    # Variables: for each day 1..17, which city (represented as an integer)
    day_city = [Int(f'day_{day}_city') for day in range(1, 18)]
    
    # Each day's city must be a valid city index (0..7)
    for day in range(17):
        s.add(day_city[day] >= 0, day_city[day] < len(city_list))
    
    # Constraints for transitions: consecutive days must be the same city or connected by a direct flight
    for day in range(16):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either stay in same city or move to connected city
        same_city = current_city == next_city
        flight_possible = Or([And(current_city == city_map[city], 
                             next_city == city_map[neighbor])
                             for city in city_list 
                             for neighbor in flight_graph[city]])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints
    for city, duration in cities.items():
        s.add(Sum([If(day_city[day] == city_map[city], 1, 0) for day in range(17)]) == duration)
    
    # Event constraints
    # Reykjavik between day 3 and 4 (must be in Reykjavik on at least one of these days)
    s.add(Or(day_city[2] == city_map['Reykjavik'], day_city[3] == city_map['Reykjavik']))
    
    # Stockholm between day 4 and 5
    s.add(Or(day_city[3] == city_map['Stockholm'], day_city[4] == city_map['Stockholm']))
    
    # Porto wedding between day 13 and 17 (must be in Porto on at least one of these days)
    s.add(Or([day_city[day] == city_map['Porto'] for day in range(12, 17)]))
    
    # Vienna workshop between day 11 and 13
    s.add(Or([day_city[day] == city_map['Vienna'] for day in range(10, 13)]))
    
    # Additional constraints to help the solver
    # Must start in some city
    # Must end in some city
    # No need to visit all cities (some might not be visited)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(17):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({'day': day + 1, 'city': city_list[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(result)