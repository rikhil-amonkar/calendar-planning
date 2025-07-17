from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')
    ]
    
    # Create flight dictionary
    flight_dict = {city: [] for city in cities}
    for city1, city2 in direct_flights:
        flight_dict[city1].append(city2)
        flight_dict[city2].append(city1)
    
    s = Solver()
    
    # Create variables for each day
    day_city = [Int(f'day_{day}') for day in range(1, 15)]
    for day in range(14):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Fixed day constraints
    s.add(day_city[0] == city_to_idx['Helsinki'])  # Day 1
    s.add(day_city[1] == city_to_idx['Helsinki'])  # Day 2
    s.add(day_city[7] == city_to_idx['Reykjavik']) # Day 8
    s.add(day_city[8] == city_to_idx['Warsaw'])    # Day 9
    s.add(day_city[9] == city_to_idx['Warsaw'])    # Day 10
    s.add(day_city[10] == city_to_idx['Warsaw'])   # Day 11
    
    # Duration constraints (accounting for flight days)
    duration_constraints = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    
    for city, duration in duration_constraints.items():
        count = Sum([If(day_city[day] == city_to_idx[city], 1, 0) for day in range(14)])
        s.add(count == duration)
    
    # Flight constraints
    for day in range(13):
        current = day_city[day]
        next_day = day_city[day + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or take a direct flight
            *[And(current == city_to_idx[city1], next_day == city_to_idx[city2])
              for city1 in flight_dict 
              for city2 in flight_dict[city1]]
        ))
    
    # Additional constraints to help solver
    # Reykjavik needs one more day besides day 8
    s.add(Or(
        Sum([If(day_city[day] == city_to_idx['Reykjavik'], 1, 0) 
             for day in [2,3,4,5,6,11,12,13]]) >= 1
    ))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(14):
            city_idx = model.eval(day_city[day]).as_long()
            itinerary.append({'day': day + 1, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)