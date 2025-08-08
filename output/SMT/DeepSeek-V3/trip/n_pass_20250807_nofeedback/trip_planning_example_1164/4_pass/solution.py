from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
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
    
    # Create a set of tuples representing direct flights
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Z3 solver
    s = Solver()
    
    # Variables: for each day 1..17, which city (represented as an integer)
    day_city = [Int(f'day_{day}_city') for day in range(1, 18)]  # days 1 to 17
    
    # Each day's city must be a valid city index (0..7)
    for day in range(17):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Constraints for transitions: consecutive days must be the same city or connected by a direct flight
    for day in range(16):
        current_city_var = day_city[day]
        next_city_var = day_city[day + 1]
        # Either stay in the same city or move to a connected city
        same_city = current_city_var == next_city_var
        flight_possible = Or([And(current_city_var == city_map[a], next_city_var == city_map[b]) for a, b in flight_pairs])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints
    for city in cities:
        total_days = Sum([If(day_city[day] == city_map[city], 1, 0) for day in range(17)])
        if city == 'Reykjavik':
            s.add(total_days == 2)
        elif city == 'Stockholm':
            s.add(total_days == 2)
        elif city == 'Porto':
            s.add(total_days == 5)
        elif city == 'Nice':
            s.add(total_days == 3)
        elif city == 'Venice':
            s.add(total_days == 4)
        elif city == 'Vienna':
            s.add(total_days == 3)
        elif city == 'Split':
            s.add(total_days == 3)
        elif city == 'Copenhagen':
            s.add(total_days == 2)
    
    # Event constraints
    # Reykjavik between day 3 and 4
    s.add(Or(day_city[2] == city_map['Reykjavik'], day_city[3] == city_map['Reykjavik']))
    
    # Stockholm between day 4 and 5
    s.add(Or(day_city[3] == city_map['Stockholm'], day_city[4] == city_map['Stockholm']))
    
    # Porto wedding between day 13 and 17
    s.add(Or([day_city[day] == city_map['Porto'] for day in range(12, 17)]))
    
    # Vienna workshop between day 11 and 13
    s.add(Or([day_city[day] == city_map['Vienna'] for day in range(10, 13)]))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(17):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({'day': day + 1, 'city': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(result)