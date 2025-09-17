import json
from z3 import *

def main():
    # City mapping
    cities = {0: 'Hamburg', 1: 'Munich', 2: 'Manchester', 3: 'Lyon', 4: 'Split'}
    
    # Direct flights (undirected)
    flights = [(0,1), (0,2), (0,4), (1,2), (1,3), (1,4), (2,4), (3,4)]
    
    # Create solver
    s = Solver()
    
    # City variables for each day (day0 to day20)
    c = [Int(f'c_{i}') for i in range(21)]
    
    # Constrain each city variable to be between 0 and 4
    for i in range(21):
        s.add(And(c[i] >= 0, c[i] <= 4))
    
    # Flight constraints: if city changes, must be connected by direct flight
    for i in range(1, 21):
        prev_city = c[i-1]
        curr_city = c[i]
        s.add(If(prev_city != curr_city, 
                 Or([And(prev_city == a, curr_city == b) for a, b in flights] + 
                    [And(prev_city == b, curr_city == a) for a, b in flights]),
                 True))
    
    # Specific day constraints
    s.add(c[13] == 3)  # Lyon on day13
    s.add(c[14] == 3)  # Lyon on day14
    s.add(c[19] == 2)  # Manchester on day19
    s.add(c[20] == 2)  # Manchester on day20
    
    # Day counting constraints
    day_count = [0]*5
    for city_idx in range(5):
        total = 0
        for i in range(1, 21):
            total += If(Or(c[i-1] == city_idx, c[i] == city_idx), 1, 0)
        day_count[city_idx] = total
    
    # Required days per city
    s.add(day_count[0] == 7)  # Hamburg
    s.add(day_count[1] == 6)  # Munich
    s.add(day_count[2] == 2)  # Manchester
    s.add(day_count[3] == 2)  # Lyon
    s.add(day_count[4] == 7)  # Split
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        # Extract city for each day (day1 to day20)
        itinerary_days = [m.evaluate(c[i]).as_long() for i in range(1,21)]
        
        # Group consecutive days with same city
        itinerary = []
        start = 1
        current_city = itinerary_days[0]
        for day in range(2, 21):
            if itinerary_days[day-1] != current_city:
                end = day - 1
                itinerary.append({
                    "day_range": f"Day {start}-{end}",
                    "place": cities[current_city]
                })
                start = day
                current_city = itinerary_days[day-1]
        itinerary.append({
            "day_range": f"Day {start}-20",
            "place": cities[current_city]
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No valid itinerary found')

if __name__ == '__main__':
    main()