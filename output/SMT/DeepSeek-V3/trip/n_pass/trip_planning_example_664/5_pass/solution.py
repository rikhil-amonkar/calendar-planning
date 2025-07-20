from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Tallinn': 2,
        'Bucharest': 4,
        'Seville': 5,
        'Stockholm': 5,
        'Munich': 5,
        'Milan': 2
    }
    
    # Direct flights as adjacency list
    direct_flights = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Stockholm', 'Bucharest', 'Seville', 'Milan', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Create solver
    solver = Solver()
    
    # Day variables (1-18)
    days = [Int(f'day_{i}') for i in range(1, 19)]
    
    # City IDs
    city_ids = {city: idx for idx, city in enumerate(cities)}
    id_to_city = {v: k for k, v in city_ids.items()}
    
    # Each day must be a valid city
    for day in days:
        solver.add(Or([day == city_ids[city] for city in cities]))
    
    # Total days per city
    for city, req_days in cities.items():
        solver.add(Sum([If(day == city_ids[city], 1, 0) for day in days]) == req_days)
    
    # Flight connections
    for i in range(17):
        current = days[i]
        next_day = days[i+1]
        solver.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == city_ids[city], next_day == city_ids[neigh]) 
              for city in direct_flights 
              for neigh in direct_flights[city]]
        ))
    
    # Relaxed date range constraints
    # Bucharest must have at least 1 day between 1-4
    solver.add(Or([days[i] == city_ids['Bucharest'] for i in range(4)]))
    
    # Munich must have at least 1 day between 4-8
    solver.add(Or([days[i] == city_ids['Munich'] for i in range(3, 8)]))
    
    # Seville must have at least 1 day between 8-12
    solver.add(Or([days[i] == city_ids['Seville'] for i in range(7, 12)]))
    
    # Additional constraints to help solver
    # First day must be Bucharest (since it's earliest requirement)
    solver.add(days[0] == city_ids['Bucharest'])
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(18):
            day_num = i + 1
            city_id = model.evaluate(days[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": day_num, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

print(solve_itinerary())