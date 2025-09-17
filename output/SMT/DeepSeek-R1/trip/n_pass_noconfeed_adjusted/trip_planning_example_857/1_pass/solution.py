from z3 import *
import json

def main():
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    n_days = 18
    n_cities = len(cities)
    
    direct_flights = set()
    connections = [
        (4, 6), (5, 2), (4, 0), (4, 1), (2, 1), (6, 1), (6, 0), (1, 0), (1, 3), (5, 3), (6, 5), (6, 3), (5, 1), (0, 3), (4, 3)
    ]
    for a, b in connections:
        direct_flights.add((min(a, b), max(a, b)))
    
    s = Solver()
    
    start_city = [Int('start_city_%d' % i) for i in range(1, n_days+1)]
    travel = [Bool('travel_%d' % i) for i in range(1, n_days+1)]
    dest_city = [Int('dest_city_%d' % i) for i in range(1, n_days+1)]
    
    for i in range(n_days):
        s.add(start_city[i] >= 0, start_city[i] < n_cities)
        s.add(dest_city[i] >= 0, dest_city[i] < n_cities)
    
    for i in range(n_days-1):
        s.add(Implies(travel[i], start_city[i] != dest_city[i]))
        s.add(Implies(travel[i], 
            Or([And(start_city[i] == a, dest_city[i] == b) for (a, b) in direct_flights] + 
               [And(start_city[i] == b, dest_city[i] == a) for (a, b) in direct_flights])))
        s.add(If(travel[i], start_city[i+1] == dest_city[i], start_city[i+1] == start_city[i]))
    
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            total += If(start_city[i] == c, 1, 0)
            total += If(And(travel[i], dest_city[i] == c), 1, 0)
        s.add(total == [2, 3, 3, 4, 5, 5, 2][c])
    
    mykonos_constraint = Or([Or(start_city[i] == 2, And(travel[i], dest_city[i] == 2)) for i in range(9, 12)])
    s.add(mykonos_constraint)
    
    manchester_constraint = Or([Or(start_city[i] == 3, And(travel[i], dest_city[i] == 3)) for i in range(14, 18)])
    s.add(manchester_constraint)
    
    for i in [4, 5]:
        s.add(Or(start_city[i] == 6, And(travel[i], dest_city[i] == 6)))
    
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start_city[i]).as_long() for i in range(n_days)]
        travel_vals = [is_true(m.evaluate(travel[i])) for i in range(n_days)]
        dest_vals = [m.evaluate(dest_city[i]).as_long() for i in range(n_days)]
        
        itinerary = []
        current_city_index = start_vals[0]
        start_day = 1
        for day in range(1, n_days):
            if start_vals[day] != current_city_index:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city_index]
                })
                current_city_index = start_vals[day]
                start_day = day + 1
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": cities[current_city_index]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()