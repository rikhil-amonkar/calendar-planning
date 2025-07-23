from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    city_rev = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Dubrovnik', 'Stockholm'), ('Lisbon', 'Copenhagen'), ('Lisbon', 'Lyon'),
        ('Copenhagen', 'Stockholm'), ('Copenhagen', 'Split'), ('Prague', 'Stockholm'),
        ('Tallinn', 'Stockholm'), ('Prague', 'Lyon'), ('Lisbon', 'Stockholm'),
        ('Prague', 'Lisbon'), ('Stockholm', 'Split'), ('Prague', 'Copenhagen'),
        ('Split', 'Lyon'), ('Copenhagen', 'Dubrovnik'), ('Prague', 'Split'),
        ('Tallinn', 'Copenhagen'), ('Tallinn', 'Prague')
    ]
    
    # Create flight connections graph
    flight_graph = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Number of days
    days = 19
    
    # Create solver
    solver = Solver()
    
    # Decision variables: city for each day (0-based)
    day_city = [Int(f'day_{i}') for i in range(days)]
    
    # Each day must be a valid city index
    for dc in day_city:
        solver.add(dc >= 0, dc < len(cities))
    
    # Flight transition constraints
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        
        # Either stay in same city or take a direct flight
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == city_rev[a], next_city == city_rev[b]) 
              for a in flight_graph for b in flight_graph[a]]
        ))
    
    # Duration constraints
    def days_in_city(city):
        return Sum([If(day_city[i] == city_rev[city], 1, 0) for i in range(days)])
    
    solver.add(days_in_city('Lisbon') == 2)
    solver.add(days_in_city('Dubrovnik') == 5)
    solver.add(days_in_city('Copenhagen') == 5)
    solver.add(days_in_city('Prague') == 3)
    solver.add(days_in_city('Tallinn') == 2)
    solver.add(days_in_city('Stockholm') == 4)
    solver.add(days_in_city('Split') == 3)
    solver.add(days_in_city('Lyon') == 2)
    
    # Event constraints
    # Workshop in Lisbon between day 4 and 5 (days 3-4 in 0-based)
    solver.add(Or(day_city[3] == city_rev['Lisbon'], day_city[4] == city_rev['Lisbon']))
    
    # Meet friend in Tallinn between day 1 and 2 (days 0-1 in 0-based)
    solver.add(Or(day_city[0] == city_rev['Tallinn'], day_city[1] == city_rev['Tallinn']))
    
    # Wedding in Stockholm between day 13 and 16 (days 12-15 in 0-based)
    solver.add(Or([day_city[i] == city_rev['Stockholm'] for i in range(12, 16)]))
    
    # Annual show in Lyon from day 18 to 19 (days 17-18 in 0-based)
    solver.add(day_city[17] == city_rev['Lyon'])
    solver.add(day_city[18] == city_rev['Lyon'])
    
    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_city[i]).as_long()
            itinerary.append({"day": i + 1, "place": cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))