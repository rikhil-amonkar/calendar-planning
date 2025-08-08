from z3 import *

def solve_itinerary():
    # Cities and their encodings
    cities = {'Riga': 0, 'Budapest': 1, 'Paris': 2, 'Warsaw': 3}
    reverse_cities = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    connections = {
        0: [2, 3],    # Riga connects to Paris and Warsaw
        1: [2, 3],     # Budapest connects to Paris and Warsaw
        2: [0, 1, 3],  # Paris connects to Riga, Budapest, Warsaw
        3: [0, 1, 2]   # Warsaw connects to Riga, Budapest, Paris
    }
    
    s = Solver()
    days = 17
    itinerary = [Int(f'day_{i}') for i in range(1, days+1)]
    
    # Each day must be one of the four cities
    for day in itinerary:
        s.add(Or([day == cities[c] for c in cities]))
    
    # Fixed days in Warsaw (1-2) and Riga (11-17)
    s.add(itinerary[0] == cities['Warsaw'])
    s.add(itinerary[1] == cities['Warsaw'])
    for i in range(10, 17):
        s.add(itinerary[i] == cities['Riga'])
    
    # Transition constraints between consecutive days
    for i in range(days-1):
        current = itinerary[i]
        next_day = itinerary[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == city, next_day == conn) 
                for city in connections 
                for conn in connections[city]])
        ))
    
    # Count days in each city
    counts = {
        'Riga': Sum([If(itinerary[i] == cities['Riga'], 1, 0) for i in range(days)]),
        'Budapest': Sum([If(itinerary[i] == cities['Budapest'], 1, 0) for i in range(days)]),
        'Paris': Sum([If(itinerary[i] == cities['Paris'], 1, 0) for i in range(days)]),
        'Warsaw': Sum([If(itinerary[i] == cities['Warsaw'], 1, 0) for i in range(days)])
    }
    
    # Add day count constraints
    s.add(counts['Riga'] == 7)
    s.add(counts['Budapest'] == 7)
    s.add(counts['Paris'] == 4)
    s.add(counts['Warsaw'] == 2)
    
    if s.check() == sat:
        model = s.model()
        result = []
        for i in range(days):
            city = model.evaluate(itinerary[i]).as_long()
            result.append({'day': i+1, 'place': reverse_cities[city]})
        
        # Verify transitions
        valid = True
        for i in range(days-1):
            current = result[i]['place']
            next_p = result[i+1]['place']
            if current != next_p:
                if cities[next_p] not in connections[cities[current]]:
                    valid = False
                    break
        if not valid:
            # Block invalid solution and try again
            s.add(Or([itinerary[i] != model.evaluate(itinerary[i]) for i in range(days)]))
            return solve_itinerary()
        
        return {'itinerary': result}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))