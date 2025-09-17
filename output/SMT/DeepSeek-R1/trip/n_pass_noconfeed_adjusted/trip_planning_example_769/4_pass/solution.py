from z3 import *
import json

def main():
    # City indices
    cities = {
        'Porto': 0,
        'Prague': 1,
        'Reykjavik': 2,
        'Santorini': 3,
        'Amsterdam': 4,
        'Munich': 5
    }
    n_days = 16
    
    # Direct flights (symmetric)
    direct_flights = set()
    connections = [
        (0,4), (5,4), (2,4), (5,0), (1,2), (2,5), (4,3), (1,4), (1,5)
    ]
    for a, b in connections:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    
    # Initialize solver
    s = Solver()
    
    # Variables for start and end city each day
    start = [Int('start_%d' % i) for i in range(n_days)]
    end = [Int('end_%d' % i) for i in range(n_days)]
    
    # Domain constraints
    for i in range(n_days):
        s.add(start[i] >= 0, start[i] <= 5)
        s.add(end[i] >= 0, end[i] <= 5)
    
    # Start and end in Porto
    s.add(start[0] == 0)
    s.add(end[n_days-1] == 0)
    
    # Continuity: end of day i is start of day i+1
    for i in range(n_days-1):
        s.add(end[i] == start[i+1])
    
    # Flight connections: if start and end are different, must be connected by a direct flight
    for i in range(n_days):
        s.add(Implies(start[i] != end[i], Or([And(start[i] == a, end[i] == b) for (a, b) in direct_flights])))
    
    # Total days per city (count end cities)
    total_days = [0] * 6
    for c in range(6):
        total_days[c] = Sum([If(end[i] == c, 1, 0) for i in range(n_days)])
    # Adjusted days to sum to 16
    s.add(total_days[0] == 3)  # Porto
    s.add(total_days[1] == 3)  # Prague
    s.add(total_days[2] == 3)  # Reykjavik
    s.add(total_days[3] == 2)  # Santorini
    s.add(total_days[4] == 2)  # Amsterdam
    s.add(total_days[5] == 3)  # Munich
    
    # Events
    # Wedding in Reykjavik between day 4-7 (indices 3-6 in zero-indexed days)
    s.add(Or([And(end[i] == 2) for i in range(3, 7)]))
    
    # Conference in Amsterdam on day 14-15 (indices 13-14)
    s.add(And(end[13] == 4, end[14] == 4))
    
    # Meeting in Munich between day 7-10 (indices 6-9)
    s.add(Or([And(end[i] == 5) for i in range(6, 10)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        start_values = [m.evaluate(start[i]).as_long() for i in range(n_days)]
        end_values = [m.evaluate(end[i]).as_long() for i in range(n_days)]
        city_names = {0: 'Porto', 1: 'Prague', 2: 'Reykjavik', 3: 'Santorini', 4: 'Amsterdam', 5: 'Munich'}
        
        # Group consecutive days by end city
        segments = []
        current_city = end_values[0]
        start_day = 1
        for day_idx in range(1, n_days):
            if end_values[day_idx] != current_city:
                segments.append({
                    'day_range': f"Day {start_day}-{day_idx}",
                    'place': city_names[current_city]
                })
                start_day = day_idx + 1
                current_city = end_values[day_idx]
        segments.append({
            'day_range': f"Day {start_day}-{n_days}",
            'place': city_names[current_city]
        })
        
        result = {'itinerary': segments}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()