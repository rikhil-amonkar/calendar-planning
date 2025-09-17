from z3 import *
import json

def main():
    # Cities: Stuttgart (0), Manchester (1), Madrid (2), Vienna (3)
    cities = ['Stuttgart', 'Manchester', 'Madrid', 'Vienna']
    n_days = 15
    graph = [(0, 3), (1, 3), (2, 3), (1, 0), (1, 2)]  # Direct flight connections

    s = Solver()
    
    # Arrays for start and end city each day
    start = [Int('start_%d' % i) for i in range(1, n_days+1)]
    end = [Int('end_%d' % i) for i in range(1, n_days+1)]
    is_travel = [Bool('is_travel_%d' % i) for i in range(1, n_days+1)]
    
    # City constraints
    for i in range(n_days):
        s.add(start[i] >= 0, start[i] <= 3)
        s.add(end[i] >= 0, end[i] <= 3)
    
    # Day constraints
    for i in range(n_days):
        s.add(Implies(Not(is_travel[i]), start[i] == end[i]))
        s.add(Implies(is_travel[i], start[i] != end[i]))
        s.add(Implies(is_travel[i], Or(
            [Or(And(start[i] == a, end[i] == b), And(start[i] == b, end[i] == a)) for a, b in graph]
        )))
    
    # Continuity between days
    for i in range(n_days-1):
        s.add(end[i] == start[i+1])
    
    # Total travel days
    s.add(Sum([If(is_travel[i], 1, 0) for i in range(n_days)]) == 3)
    
    # Day counts per city
    counts = [0] * 4
    for c in range(4):
        total = 0
        for i in range(n_days):
            # For non-travel days: count if city matches
            non_travel_count = If(And(Not(is_travel[i]), start[i] == c), 1, 0)
            # For travel days: count if start or end city matches
            travel_count = If(And(is_travel[i], Or(start[i] == c, end[i] == c)), 1, 0)
            total += non_travel_count + travel_count
        s.add(total == [5, 7, 4, 2][c])
    
    # Workshop in Stuttgart between day 11-15
    s.add(Or([Or(start[i] == 0, end[i] == 0) for i in range(10, 15)]))
    # Wedding in Manchester between day 1-7
    s.add(Or([Or(start[i] == 1, end[i] == 1) for i in range(0, 7)]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        overnight_cities = []
        for i in range(n_days):
            overnight_cities.append(m.evaluate(end[i]).as_long())
        
        # Group consecutive days with same city
        itinerary = []
        start_day = 1
        current_city = overnight_cities[0]
        for day in range(1, n_days):
            if overnight_cities[day] != current_city:
                end_day = day
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': cities[current_city]
                })
                start_day = day + 1
                current_city = overnight_cities[day]
        itinerary.append({
            'day_range': f"Day {start_day}-{n_days}",
            'place': cities[current_city]
        })
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()