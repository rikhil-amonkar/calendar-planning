from z3 import *
import json

def solve_itinerary():
    # Cities with their indices
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flights = [
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
    flight_pairs = set()
    for a, b in flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
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
    # Workshop in Lisbon between day 4-5
    solver.add(Or(days[3] == city_idx['Lisbon'], days[4] == city_idx['Lisbon']))
    
    # Meet friend in Tallinn between day 1-2
    solver.add(Or(days[0] == city_idx['Tallinn'], days[1] == city_idx['Tallinn']))
    
    # Wedding in Stockholm between day 13-16
    solver.add(Or([days[i] == city_idx['Stockholm'] for i in range(12, 16)]))
    
    # Annual show in Lyon on days 18-19
    solver.add(days[17] == city_idx['Lyon'])
    solver.add(days[18] == city_idx['Lyon'])
    
    # Flight constraints
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        # If changing cities, must have a direct flight
        solver.add(Implies(current != next_day, 
                          Or([And(current == city_idx[a], next_day == city_idx[b]) 
                             for a, b in flight_pairs])))
    
    # Additional constraints to help guide the solver
    # Avoid too many city changes
    solver.add(Sum([If(days[i] != days[i+1], 1, 0) for i in range(len(days)-1)]) <= 10)
    
    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 20):
            city_idx = model[days[i-1]].as_long()
            itinerary.append({'day': i, 'place': cities[city_idx]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        # Print verification
        print("City days verification:")
        for city, days in city_days.items():
            print(f"{city}: {days} days (target: {duration[city]})")
        
        return {'itinerary': itinerary}
    else:
        print("No solution found")
        return None

# Solve and print the itinerary
result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))