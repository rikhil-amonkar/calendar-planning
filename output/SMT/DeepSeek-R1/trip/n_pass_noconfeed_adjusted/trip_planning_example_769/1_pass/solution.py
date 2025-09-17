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
    start = [Int('start_%d' % i) for i in range(1, n_days+1)]
    end = [Int('end_%d' % i) for i in range(1, n_days+1)]
    
    # Domain constraints
    for i in range(n_days):
        s.add(start[i] >= 0, start[i] <= 5)
        s.add(end[i] >= 0, end[i] <= 5)
    
    # Continuity: end of day i is start of day i+1
    for i in range(n_days-1):
        s.add(end[i] == start[i+1])
    
    # Flight connections
    for i in range(n_days):
        cond = Or([And(start[i] == a, end[i] == b) for (a, b) in direct_flights])
        s.add(Implies(start[i] != end[i], cond))
    
    # Total days per city
    total_days = [0] * 6
    for c in range(6):
        total_days[c] = Sum([If(Or(start[i] == c, end[i] == c), 1, 0) for i in range(n_days)])
    s.add(total_days[0] == 5)  # Porto
    s.add(total_days[1] == 4)  # Prague
    s.add(total_days[2] == 4)  # Reykjavik
    s.add(total_days[3] == 2)  # Santorini
    s.add(total_days[4] == 2)  # Amsterdam
    s.add(total_days[5] == 4)  # Munich
    
    # Events
    # Wedding in Reykjavik between day 4-7 (indices 3-6)
    wedding_constraints = [And(start[i] == 2, end[i] == 2) for i in range(3, 7)]
    s.add(Or(wedding_constraints))
    
    # Conference in Amsterdam on day 14-15 (indices 13-14)
    s.add(And(start[13] == 4, end[13] == 4))
    s.add(And(start[14] == 4, end[14] == 4))
    
    # Meeting in Munich between day 7-10 (indices 6-9)
    meeting_constraints = [And(start[i] == 5, end[i] == 5) for i in range(6, 10)]
    s.add(Or(meeting_constraints))
    
    # Solve
    if s.check() == sat:
        m = s.model()
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