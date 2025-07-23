from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Riga', 'Budapest', 'Paris', 'Warsaw']
    
    # Create solver
    s = Solver()
    
    # Day variables (1-17)
    days = [Int(f'day_{i}') for i in range(1, 18)]
    
    # Each day must be one of the cities (0-3)
    for day in days:
        s.add(day >= 0, day <= 3)
    
    # Direct flight connections (undirected)
    connections = {
        0: [2, 3],  # Riga connects to Paris and Warsaw
        1: [2, 3],   # Budapest connects to Paris and Warsaw
        2: [0, 1, 3], # Paris connects to Riga, Budapest, Warsaw
        3: [0, 1, 2]  # Warsaw connects to Riga, Budapest, Paris
    }
    
    # Flight constraints between consecutive days
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([next_day == c for c in connections[current.as_long() if isinstance(current, int)]),
            Or([And(current == city, Or([next_day == c for c in conn])) 
                for city, conn in connections.items()])
        ))
    
    # Fixed events
    s.add(days[0] == 3)  # Day 1 in Warsaw
    s.add(days[1] == 3)  # Day 2 in Warsaw
    
    # Days 11-17 in Riga
    for i in range(10, 17):
        s.add(days[i] == 0)
    
    # Total days per city
    s.add(Sum([If(d == 0, 1, 0) for d in days]) == 7)  # Riga
    s.add(Sum([If(d == 1, 1, 0) for d in days]) == 7)  # Budapest
    s.add(Sum([If(d == 2, 1, 0) for d in days]) == 4)  # Paris
    s.add(Sum([If(d == 3, 1, 0) for d in days]) == 2)  # Warsaw
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(17):
            day = i+1
            city = cities[m.evaluate(days[i]).as_long()]
            itinerary.append({'day': day, 'place': city})
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")