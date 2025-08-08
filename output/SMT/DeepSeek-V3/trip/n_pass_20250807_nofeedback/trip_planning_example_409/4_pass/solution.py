from z3 import *
import json

def solve_itinerary():
    # Cities with consistent naming
    cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']
    city_map = {c: i for i, c in enumerate(cities)}
    
    # Direct flights based on problem statement
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Hamburg': ['Bucharest', 'Helsinki', 'Zurich', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    days = 12
    s = Solver()
    
    # Create day variables (0-based index)
    city_vars = [Int(f'day_{i}') for i in range(days)]
    
    # Each day must be a valid city index
    for day in city_vars:
        s.add(day >= 0, day < len(cities))
    
    # City day count constraints
    s.add(Sum([If(city_vars[i] == city_map['Hamburg'], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(city_vars[i] == city_map['Zurich'], 1, 0) for i in range(days)]) == 3)
    s.add(Sum([If(city_vars[i] == city_map['Helsinki'], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(city_vars[i] == city_map['Bucharest'], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(city_vars[i] == city_map['Split'], 1, 0) for i in range(days)]) == 7)
    
    # Conference days in Split (day 4 and 10, 0-based)
    s.add(city_vars[3] == city_map['Split'])
    s.add(city_vars[9] == city_map['Split'])
    
    # Wedding in Zurich between day 1 and 3 (0-based)
    s.add(Or(
        city_vars[0] == city_map['Zurich'],
        city_vars[1] == city_map['Zurich'],
        city_vars[2] == city_map['Zurich']
    ))
    
    # Flight constraints
    for i in range(days - 1):
        current = city_vars[i]
        next_ = city_vars[i + 1]
        # Either stay or fly directly
        s.add(Or(
            current == next_,
            *[
                And(current == city_map[current_city], next_ == city_map[next_city])
                for current_city in direct_flights
                for next_city in direct_flights[current_city]
            ]
        ))
    
    # Additional constraints to help find a solution
    # Ensure we don't have impossible transitions
    # For example, don't jump between non-connected cities
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day = i + 1  # Convert to 1-based day numbering
            city_idx = m.evaluate(city_vars[i]).as_long()
            itinerary.append({'day': day, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        # If no solution found, try relaxing some constraints
        # For example, allow more flexibility in day counts
        s.push()
        s.add(Sum([If(city_vars[i] == city_map['Split'], 1, 0) for i in range(days)]) >= 7)
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for i in range(days):
                day = i + 1
                city_idx = m.evaluate(city_vars[i]).as_long()
                itinerary.append({'day': day, 'place': cities[city_idx]})
            return {'itinerary': itinerary}
        else:
            return {'error': 'No valid itinerary found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))