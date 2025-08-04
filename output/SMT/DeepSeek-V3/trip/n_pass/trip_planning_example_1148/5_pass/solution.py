from z3 import *
import json

def solve_itinerary():
    # Cities with their indices
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flight_pairs = [
        ('Dubrovnik', 'Stockholm'),
        ('Dubrovnik', 'Copenhagen'),
        ('Lisbon', 'Copenhagen'), 
        ('Lisbon', 'Lyon'),
        ('Lisbon', 'Stockholm'),
        ('Lisbon', 'Prague'),
        ('Copenhagen', 'Stockholm'),
        ('Copenhagen', 'Split'),
        ('Copenhagen', 'Prague'),
        ('Copenhagen', 'Tallinn'),
        ('Prague', 'Stockholm'),
        ('Prague', 'Lyon'),
        ('Prague', 'Split'),
        ('Prague', 'Tallinn'),
        ('Tallinn', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Lyon')
    ]
    
    # Make flights bidirectional
    flights = set()
    for a, b in flight_pairs:
        flights.add((a, b))
        flights.add((b, a))
    
    solver = Solver()
    
    # Variables: day_1 to day_19
    days = [Int(f'day_{i}') for i in range(1, 20)]
    
    # Each day must be assigned to a city
    for day in days:
        solver.add(day >= 0, day < len(cities))
    
    # Duration constraints
    duration = {
        'Lisbon': 2,
        'Dubrovnik': 5,
        'Copenhagen': 5,
        'Prague': 3,
        'Tallinn': 2,
        'Stockholm': 4,
        'Split': 3,
        'Lyon': 2
    }
    
    for city, count in duration.items():
        solver.add(Sum([If(day == city_idx[city], 1, 0) for day in days]) == count)
    
    # Event constraints
    # Workshop in Lisbon between day 4-5 (must be in Lisbon on day 4 or 5)
    solver.add(Or(days[3] == city_idx['Lisbon'], days[4] == city_idx['Lisbon']))
    
    # Meet friend in Tallinn between day 1-2 (must be in Tallinn on day 1 or 2)
    solver.add(Or(days[0] == city_idx['Tallinn'], days[1] == city_idx['Tallinn']))
    
    # Wedding in Stockholm between day 13-16 (must be in Stockholm on at least one of these days)
    solver.add(Or([days[i] == city_idx['Stockholm'] for i in range(12, 16)]))
    
    # Annual show in Lyon on days 18-19 (must be in Lyon both days)
    solver.add(days[17] == city_idx['Lyon'])
    solver.add(days[18] == city_idx['Lyon'])
    
    # Flight constraints
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        # If changing cities, must have a direct flight
        solver.add(Implies(current != next_day, 
                          Or([And(current == city_idx[a], next_day == city_idx[b]) 
                             for a, b in flights])))
    
    # Additional constraints to help guide the solver
    # Prefer longer stays in cities
    for i in range(1, len(days)-1):
        solver.add(Implies(days[i] != days[i-1], days[i] == days[i+1]))
    
    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 20):
            city_index = model[days[i-1]].as_long()
            itinerary.append({'day': i, 'place': cities[city_index]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        # Verify flight connections
        valid_flights = True
        for i in range(len(itinerary)-1):
            current = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current != next_city and (current, next_city) not in flights:
                valid_flights = False
                break
        
        if valid_flights and all(city_days[city] == duration[city] for city in cities):
            return {'itinerary': itinerary}
        else:
            print("Found solution but failed verification")
            return None
    else:
        print("No solution found")
        return None

# Solve and print the itinerary
result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("Failed to find a valid itinerary")