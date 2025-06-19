import json
from z3 import *

def main():
    Cities = ['Copenhagen', 'Geneva', 'Mykonos', 'Naples', 'Prague', 'Dubrovnik', 'Athens', 'Santorini', 'Brussels', 'Munich']
    
    durations = {
        'Copenhagen': 5,
        'Geneva': 3,
        'Mykonos': 2,
        'Naples': 4,
        'Prague': 2,
        'Dubrovnik': 3,
        'Athens': 4,
        'Santorini': 5,
        'Brussels': 4,
        'Munich': 5
    }
    
    flights_str = "Copenhagen and Dubrovnik, Brussels and Copenhagen, Prague and Geneva, Athens and Geneva, Naples and Dubrovnik, Athens and Dubrovnik, Geneva and Mykonos, Naples and Mykonos, Naples and Copenhagen, Munich and Mykonos, Naples and Athens, Prague and Athens, Santorini and Geneva, Athens and Santorini, Naples and Munich, Prague and Copenhagen, Brussels and Naples, Athens and Mykonos, Athens and Copenhagen, Naples and Geneva, Dubrovnik and Munich, Brussels and Munich, Prague and Brussels, Brussels and Athens, Athens and Munich, Geneva and Munich, Copenhagen and Munich, Brussels and Geneva, Copenhagen and Geneva, Prague and Munich, Copenhagen and Santorini, Naples and Santorini, Geneva and Dubrovnik"
    flight_pairs = [s.split(' and ') for s in flights_str.split(', ')]
    allowed_directed = set()
    for a, b in flight_pairs:
        allowed_directed.add((a, b))
        allowed_directed.add((b, a))
    
    solver = Solver()
    
    start = {c: Int(f'start_{c}') for c in Cities}
    end = {c: Int(f'end_{c}') for c in Cities}
    order = {c: Int(f'order_{c}') for c in Cities}
    
    for c in Cities:
        solver.add(end[c] == start[c] + durations[c] - 1)
        solver.add(start[c] >= 1, end[c] <= 28)
    
    solver.add(start['Mykonos'] == 27, end['Mykonos'] == 28)
    
    solver.add(Distinct([order[c] for c in Cities]))
    for c in Cities:
        solver.add(order[c] >= 0, order[c] <= 9)
    
    first_city_constraint = Or([And(order[c] == 0, start[c] == 1) for c in Cities])
    last_city_constraint = Or([And(order[c] == 9, end[c] == 28) for c in Cities])
    solver.add(first_city_constraint, last_city_constraint)
    
    for c1 in Cities:
        for c2 in Cities:
            if c1 == c2:
                continue
            solver.add(Implies(order[c1] + 1 == order[c2], end[c1] == start[c2]))
            if (c1, c2) not in allowed_directed:
                solver.add(order[c1] + 1 != order[c2])
    
    solver.add(start['Copenhagen'] <= 15, end['Copenhagen'] >= 11)
    solver.add(start['Naples'] <= 8, end['Naples'] >= 5)
    solver.add(start['Athens'] <= 11, end['Athens'] >= 8)
    
    if solver.check() == sat:
        m = solver.model()
        start_vals = {c: m.eval(start[c]).as_long() for c in Cities}
        end_vals = {c: m.eval(end[c]).as_long() for c in Cities}
        order_vals = {c: m.eval(order[c]).as_long() for c in Cities}
        
        sorted_cities = sorted(Cities, key=lambda c: order_vals[c])
        
        itinerary = []
        for idx, c in enumerate(sorted_cities):
            s = start_vals[c]
            e = end_vals[c]
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            itinerary.append({"day_range": day_range_str, "place": c})
            
            if idx < len(sorted_cities) - 1:
                flight_day = e
                itinerary.append({"day_range": f"Day {flight_day}", "place": c})
                next_city = sorted_cities[idx + 1]
                itinerary.append({"day_range": f"Day {flight_day}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()