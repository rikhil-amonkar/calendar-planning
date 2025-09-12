import json
from z3 import *

def main():
    # City mapping
    cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
    city_dict = {c: i for i, c in enumerate(cities)}
    
    # Direct flights (undirected)
    edges = [
        (5, 1), (5, 7), (7, 6), (3, 2), (5, 6), (5, 3), (3, 1),
        (4, 3), (4, 6), (5, 4), (1, 7), (6, 0), (5, 2), (1, 2),
        (3, 7), (2, 7), (3, 6)
    ]
    
    # Create solver
    s = Solver()
    
    # Variables for each day (1-indexed)
    start = [Int('start_%d' % i) for i in range(1, 19)]
    fly = [Bool('fly_%d' % i) for i in range(1, 19)]
    end = [Int('end_%d' % i) for i in range(1, 19)]
    
    # Constraints for each day
    for i in range(18):
        # City indices are between 0 and 7
        s.add(start[i] >= 0, start[i] <= 7)
        s.add(end[i] >= 0, end[i] <= 7)
        
        # If not flying, end_i equals start_i
        s.add(Implies(Not(fly[i]), end[i] == start[i]))
        
        # If flying, end_i != start_i and there is a direct flight
        if i < 17:
            s.add(start[i+1] == end[i])
        for a, b in edges:
            s.add(Implies(And(fly[i], start[i] == a, end[i] == b), True))
            s.add(Implies(And(fly[i], start[i] == b, end[i] == a), True))
        # Ensure flight exists if flying
        s.add(Implies(fly[i], Or([Or(And(start[i] == a, end[i] == b), And(start[i] == b, end[i] == a)) for a, b in edges])))
    
    # Total days per city
    city_days = [0] * 8
    for c in range(8):
        count = 0
        for i in range(18):
            count += If(Or(start[i] == c, And(fly[i], end[i] == c)), 1, 0)
        city_days[c] = count
    
    s.add(city_days[city_dict['Mykonos']] == 4)
    s.add(city_days[city_dict['Krakow']] == 5)
    s.add(city_days[city_dict['Vilnius']] == 2)
    s.add(city_days[city_dict['Helsinki']] == 2)
    s.add(city_days[city_dict['Dubrovnik']] == 3)
    s.add(city_days[city_dict['Oslo']] == 2)
    s.add(city_days[city_dict['Madrid']] == 5)
    s.add(city_days[city_dict['Paris']] == 2)
    
    # Specific constraints
    # Mykonos between day 15 and 18
    for i in range(18):
        in_mykonos = Or(start[i] == city_dict['Mykonos'], And(fly[i], end[i] == city_dict['Mykonos']))
        if i < 14:  # Days 1-14 (0-indexed: 0-13)
            s.add(Not(in_mykonos))
        else:  # Days 15-18 (0-indexed: 14-17)
            pass  # Allowed
    
    # Dubrovnik on days 2-4 (0-indexed: days 1,2,3)
    for i in [1, 2, 3]:
        s.add(Or(start[i] == city_dict['Dubrovnik'], And(fly[i], end[i] == city_dict['Dubrovnik'])))
    
    # Oslo on day 1 or 2 (0-indexed: days 0,1)
    oslo_days = []
    for i in [0, 1]:
        oslo_days.append(Or(start[i] == city_dict['Oslo'], And(fly[i], end[i] == city_dict['Oslo'])))
    s.add(Or(oslo_days))
    
    # Total flight days
    total_flights = Sum([If(fly[i], 1, 0) for i in range(18)])
    s.add(total_flights == 7)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Get the sleep city for each day (end_i)
        sleep_cities = []
        for i in range(18):
            sleep_cities.append(m.evaluate(end[i]).as_long())
        
        # Group consecutive days with the same sleep city
        itinerary = []
        start_day = 1
        current_city = sleep_cities[0]
        for i in range(1, 18):
            if sleep_cities[i] != current_city:
                end_day = i
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                start_day = i+1
                current_city = sleep_cities[i]
        itinerary.append({
            "day_range": f"Day {start_day}-18",
            "place": cities[current_city]
        })
        
        # Output JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()