import json
from z3 import *

def main():
    cities = {0: 'Hamburg', 1: 'Munich', 2: 'Manchester', 3: 'Lyon', 4: 'Split'}
    flights = [(0,1), (0,2), (0,4), (1,2), (1,3), (1,4), (2,4), (3,4)]
    
    s = Solver()
    # Variables for days 1 to 20 (index 0 to 19)
    c = [Int(f'c_{i}') for i in range(20)]
    
    # Each day's city is between 0 and 4
    for i in range(20):
        s.add(And(c[i] >= 0, c[i] <= 4))
    
    # Flight constraints between consecutive days
    for i in range(19):
        s.add(If(c[i] != c[i+1], 
                 Or([And(c[i] == a, c[i+1] == b) for a, b in flights] + 
                    [And(c[i] == b, c[i+1] == a) for a, b in flights]),
                 True))
    
    # Specific day constraints
    s.add(c[12] == 3)  # Day 13 is Lyon
    s.add(c[13] == 3)  # Day 14 is Lyon
    s.add(c[18] == 2)  # Day 19 is Manchester
    s.add(c[19] == 2)  # Day 20 is Manchester
    
    # Count days per city
    counts = [Sum([If(c[i] == j, 1, 0) for i in range(20)]) for j in range(5)]
    s.add(counts[0] == 7)  # Hamburg
    s.add(counts[1] == 6)  # Munich
    s.add(counts[2] == 2)  # Manchester
    s.add(counts[3] == 2)  # Lyon
    s.add(counts[4] == 7)  # Split
    
    if s.check() == sat:
        m = s.model()
        itinerary_days = [m.evaluate(c[i]).as_long() for i in range(20)]
        
        itinerary = []
        start = 1
        current_city = itinerary_days[0]
        for day in range(1, 20):
            if itinerary_days[day] != current_city:
                end = day
                itinerary.append({
                    "day_range": f"Day {start}-{end}",
                    "place": cities[current_city]
                })
                start = day + 1
                current_city = itinerary_days[day]
        itinerary.append({
            "day_range": f"Day {start}-20",
            "place": cities[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No valid itinerary found')

if __name__ == '__main__':
    main()