import json
from z3 import *

def main():
    # City to index mapping
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Required days per city
    req_days = [2, 5, 5, 3, 2, 4, 3, 2]
    
    # Direct flights (undirected)
    flights = [
        (1, 5), (5, 1),  # Dubrovnik-Stockholm
        (0, 2), (2, 0),  # Lisbon-Copenhagen
        (0, 7), (7, 0),  # Lisbon-Lyon
        (2, 5), (5, 2),  # Copenhagen-Stockholm
        (2, 6), (6, 2),  # Copenhagen-Split
        (3, 5), (5, 3),  # Prague-Stockholm
        (4, 5), (5, 4),  # Tallinn-Stockholm
        (3, 7), (7, 3),  # Prague-Lyon
        (0, 5), (5, 0),  # Lisbon-Stockholm
        (3, 0), (0, 3),  # Prague-Lisbon
        (5, 6), (6, 5),  # Stockholm-Split
        (3, 2), (2, 3),  # Prague-Copenhagen
        (6, 7), (7, 6),  # Split-Lyon
        (2, 1), (1, 2),  # Copenhagen-Dubrovnik
        (3, 6), (6, 3),  # Prague-Split
        (4, 2), (2, 4),  # Tallinn-Copenhagen
        (4, 3), (3, 4)   # Tallinn-Prague
    ]
    
    # Event constraints: day -> city
    events = {
        1: 'Tallinn',
        2: 'Tallinn',
        4: 'Lisbon',
        5: 'Lisbon',
        13: 'Stockholm',
        14: 'Stockholm',
        15: 'Stockholm',
        16: 'Stockholm',
        18: 'Lyon',
        19: 'Lyon'
    }
    
    n_days = 19
    n_cities = len(cities)
    
    # Z3 solver
    s = Solver()
    
    # Variables: x[i] is the city index for day i (1-indexed)
    x = [Int(f'x_{i}') for i in range(1, n_days+1)]
    for i in range(n_days):
        s.add(And(x[i] >= 0, x[i] < n_cities))
    
    # travel[i] indicates if we travel on day i (from day i to day i+1)
    travel = [Bool(f'travel_{i}') for i in range(1, n_days)]
    
    # Constraint: travel[i] is true iff x[i] != x[i+1]
    for i in range(n_days-1):
        s.add(travel[i] == (x[i] != x[i+1]))
    
    # Constraint: if travel[i] is true, then (x[i], x[i+1]) must be in flights
    for i in range(n_days-1):
        cond = Implies(travel[i], Or([And(x[i] == a, x[i+1] == b) for a, b in flights]))
        s.add(cond)
    
    # Constraint: total days per city must match required days
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            # Count day i if x[i] == c
            total += If(x[i] == c, 1, 0)
        for i in range(n_days-1):
            # Count travel day i if we go to city c on day i (x[i+1] == c) and travel[i] is true
            total += If(And(travel[i], x[i+1] == c), 1, 0)
        s.add(total == req_days[c])
    
    # Event constraints: must be in the event city on the specified day
    for day, city in events.items():
        c = city_index[city]
        # in_city[day, c] = (x[day-1] == c) OR (travel[day-1] and x[day] == c) for day>1? 
        # But note: our x array is 0-indexed for days 1..19, so x[day-1] is the city for day 'day'
        # For day i, we are in city c if:
        #   x[i-1] == c  OR (travel[i-1] is true and x[i] == c)   [for i>=2]
        # For day1: only x[0] == c
        if day == 1:
            s.add(x[0] == c)
        else:
            # Day i: we are in city c if either:
            #   - We sleep in city c on day i (x[day-1] == c)
            #   - We travel on day i-1 and arrive at city c (x[day-1] == c) [but note: travel[i-2] for day i?]
            # Actually, according to our model: for day i, we are in:
            #   x[i-1] (always) and if travel[i-1] is true then also x[i] (which is the next day's city)
            # But wait: our travel array is for day i (travel from day i to i+1), so for day i, the travel that affects it is travel[i-1] (if i>1) and travel[i] (if i<n_days).
            # We defined: in_city[i, c] = (x[i-1] == c) OR (travel[i-1] and (x[i] == c)) for i from 1 to n_days, but note for i=1, travel[0] is defined.
            # So for day i (1-indexed), we have:
            #   in_city[i] includes x[i-1] and if travel[i-1] is true then also x[i] (which is the city of day i+1)
            # But note: the event constraints require that we are in the city on that day, so for day i, we require that either:
            #   x[i-1] == c   OR   (travel[i-1] and x[i] == c)   [for i from 1 to n_days-1]
            # For day n_days, we only have x[n_days-1] and no travel[n_days-1] (since travel has length n_days-1)
            if day < n_days:
                s.add(Or(x[day-1] == c, And(travel[day-1], x[day] == c)))
            else:
                s.add(x[day-1] == c)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Get the city for each day
        itinerary = []
        day_assignments = []
        for i in range(n_days):
            city_idx = m.evaluate(x[i]).as_long()
            day_assignments.append(cities[city_idx])
        
        # Group consecutive days with the same city
        current_city = day_assignments[0]
        start_day = 1
        for day in range(1, n_days):
            if day_assignments[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current_city
                })
                current_city = day_assignments[day]
                start_day = day + 1
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": current_city
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()