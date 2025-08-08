from z3 import *

def solve_itinerary():
    # Cities with correct spelling
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Corrected direct flights with proper city names
    direct_flights = [
        (city_map['Dubrovnik'], city_map['Stockholm']),
        (city_map['Lisbon'], city_map['Copenhagen']),
        (city_map['Lisbon'], city_map['Lyon']),
        (city_map['Copenhagen'], city_map['Stockholm']),
        (city_map['Copenhagen'], city_map['Split']),
        (city_map['Prague'], city_map['Stockholm']),
        (city_map['Tallinn'], city_map['Stockholm']),
        (city_map['Prague'], city_map['Lyon']),
        (city_map['Lisbon'], city_map['Stockholm']),
        (city_map['Prague'], city_map['Lisbon']),
        (city_map['Stockholm'], city_map['Split']),
        (city_map['Prague'], city_map['Copenhagen']),
        (city_map['Split'], city_map['Lyon']),
        (city_map['Copenhagen'], city_map['Dubrovnik']),
        (city_map['Prague'], city_map['Split']),
        (city_map['Tallinn'], city_map['Copenhagen']),
        (city_map['Tallinn'], city_map['Prague'])
    ]
    
    # Create flight pairs for both directions
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    solver = Solver()
    
    # Day variables (1-19)
    days = [Int(f'day_{i}') for i in range(1, 20)]
    
    # Each day must be a valid city
    for day in days:
        solver.add(day >= 0, day < len(cities))
    
    # Flight constraints between consecutive days
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        solver.add(
            Implies(
                current != next_day,
                Or([And(current == a, next_day == b) for (a,b) in flight_pairs])
            )
        )
    
    # Duration constraints
    durations = {
        'Lisbon': 2,
        'Dubrovnik': 5,
        'Copenhagen': 5,
        'Prague': 3,
        'Tallinn': 2,
        'Stockholm': 4,
        'Split': 3,
        'Lyon': 2
    }
    
    for city, duration in durations.items():
        solver.add(
            Sum([If(days[i] == city_map[city], 1, 0) for i in range(19)]) == duration
        )
    
    # Event constraints
    # Lisbon workshop between day 4-5
    solver.add(Or(days[3] == city_map['Lisbon'], days[4] == city_map['Lisbon']))
    
    # Tallinn meeting day 1-2
    solver.add(Or(days[0] == city_map['Tallinn'], days[1] == city_map['Tallinn']))
    
    # Stockholm wedding day 13-16
    solver.add(Or([days[i] == city_map['Stockholm'] for i in range(12, 16)]))
    
    # Lyon show day 18-19
    solver.add(days[17] == city_map['Lyon'])
    solver.add(days[18] == city_map['Lyon'])
    
    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(19):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city_name = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city_name})
        
        # Print the itinerary
        import json
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No valid itinerary found")

solve_itinerary()