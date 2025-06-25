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
    
    splits = [
        {
            'group1': ['Santorini'],
            'group2': ['Geneva', 'Prague', 'Dubrovnik', 'Brussels', 'Munich']
        },
        {
            'group1': ['Munich'],
            'group2': ['Geneva', 'Prague', 'Dubrovnik', 'Brussels', 'Santorini']
        },
        {
            'group1': ['Prague', 'Brussels'],
            'group2': ['Geneva', 'Dubrovnik', 'Santorini', 'Munich']
        }
    ]
    
    found_solution = False
    result_itinerary = None
    
    for split in splits:
        group1 = split['group1']
        group2 = split['group2']
        
        solver = Solver()
        
        start1 = {c: Int(f'start1_{c}') for c in group1}
        end1 = {c: Int(f'end1_{c}') for c in group1}
        order1 = {c: Int(f'order1_{c}') for c in group1}
        
        for c in group1:
            solver.add(end1[c] == start1[c] + durations[c] - 1)
            solver.add(start1[c] >= 1, end1[c] <= 28)
        
        solver.add(Distinct([order1[c] for c in group1]))
        for c in group1:
            solver.add(order1[c] >= 0, order1[c] < len(group1))
        
        first_city1 = Or([And(order1[c] == 0, start1[c] == 1) for c in group1])
        last_city1 = Or([And(order1[c] == len(group1)-1, end1[c] == 5) for c in group1])
        solver.add(first_city1, last_city1)
        
        for i in range(len(group1)-1):
            for c1 in group1:
                for c2 in group1:
                    if c1 == c2:
                        continue
                    solver.add(Implies(And(order1[c1] == i, order1[c2] == i+1), end1[c1] == start1[c2]))
                    if (c1, c2) not in allowed_directed:
                        solver.add(Not(And(order1[c1] == i, order1[c2] == i+1)))
        
        for c in group1:
            solver.add(Implies(order1[c] == len(group1)-1, (c, 'Naples') in allowed_directed))
        
        start2 = {c: Int(f'start2_{c}') for c in group2}
        end2 = {c: Int(f'end2_{c}') for c in group2}
        order2 = {c: Int(f'order2_{c}') for c in group2}
        
        for c in group2:
            solver.add(end2[c] == start2[c] + durations[c] - 1)
            solver.add(start2[c] >= 1, end2[c] <= 28)
        
        solver.add(Distinct([order2[c] for c in group2]))
        for c in group2:
            solver.add(order2[c] >= 0, order2[c] < len(group2))
        
        first_city2 = Or([And(order2[c] == 0, start2[c] == 15) for c in group2])
        last_city2 = Or([And(order2[c] == len(group2)-1, end2[c] == 27) for c in group2])
        solver.add(first_city2, last_city2)
        
        for i in range(len(group2)-1):
            for c1 in group2:
                for c2 in group2:
                    if c1 == c2:
                        continue
                    solver.add(Implies(And(order2[c1] == i, order2[c2] == i+1), end2[c1] == start2[c2]))
                    if (c1, c2) not in allowed_directed:
                        solver.add(Not(And(order2[c1] == i, order2[c2] == i+1)))
        
        for c in group2:
            solver.add(Implies(order2[c] == 0, ('Copenhagen', c) in allowed_directed))
            solver.add(Implies(order2[c] == len(group2)-1, (c, 'Mykonos') in allowed_directed))
        
        if solver.check() == sat:
            m = solver.model()
            start1_vals = {c: m.eval(start1[c]).as_long() for c in group1}
            end1_vals = {c: m.eval(end1[c]).as_long() for c in group1}
            order1_vals = {c: m.eval(order1[c]).as_long() for c in group1}
            
            sorted_group1 = sorted(group1, key=lambda c: order1_vals[c])
            
            start2_vals = {c: m.eval(start2[c]).as_long() for c in group2}
            end2_vals = {c: m.eval(end2[c]).as_long() for c in group2}
            order2_vals = {c: m.eval(order2[c]).as_long() for c in group2}
            
            sorted_group2 = sorted(group2, key=lambda c: order2_vals[c])
            
            itinerary = []
            
            for idx, c in enumerate(sorted_group1):
                s = start1_vals[c]
                e = end1_vals[c]
                if s == e:
                    day_range_str = f"Day {s}"
                else:
                    day_range_str = f"Day {s}-{e}"
                itinerary.append({"day_range": day_range_str, "place": c})
                if idx < len(sorted_group1) - 1:
                    flight_day = e
                    itinerary.append({"day_range": f"Day {flight_day}", "place": c})
                    next_city = sorted_group1[idx + 1]
                    itinerary.append({"day_range": f"Day {flight_day}", "place": next_city})
                else:
                    flight_day = e
                    itinerary.append({"day_range": f"Day {flight_day}", "place": c})
                    itinerary.append({"day_range": f"Day {flight_day}", "place": "Naples"})
            
            naples_stay = {"day_range": "Day 5-8", "place": "Naples"}
            itinerary.append(naples_stay)
            itinerary.append({"day_range": "Day 8", "place": "Naples"})
            itinerary.append({"day_range": "Day 8", "place": "Athens"})
            
            athens_stay = {"day_range": "Day 8-11", "place": "Athens"}
            itinerary.append(athens_stay)
            itinerary.append({"day_range": "Day 11", "place": "Athens"})
            itinerary.append({"day_range": "Day 11", "place": "Copenhagen"})
            
            copenhagen_stay = {"day_range": "Day 11-15", "place": "Copenhagen"}
            itinerary.append(copenhagen_stay)
            itinerary.append({"day_range": "Day 15", "place": "Copenhagen"})
            first_city_group2 = sorted_group2[0]
            itinerary.append({"day_range": "Day 15", "place": first_city_group2})
            
            for idx, c in enumerate(sorted_group2):
                s = start2_vals[c]
                e = end2_vals[c]
                if s == e:
                    day_range_str = f"Day {s}"
                else:
                    day_range_str = f"Day {s}-{e}"
                itinerary.append({"day_range": day_range_str, "place": c})
                if idx < len(sorted_group2) - 1:
                    flight_day = e
                    itinerary.append({"day_range": f"Day {flight_day}", "place": c})
                    next_city = sorted_group2[idx + 1]
                    itinerary.append({"day_range": f"Day {flight_day}", "place": next_city})
                else:
                    flight_day = e
                    itinerary.append({"day_range": f"Day {flight_day}", "place": c})
                    itinerary.append({"day_range": f"Day {flight_day}", "place": "Mykonos"})
            
            mykonos_stay = {"day_range": "Day 27-28", "place": "Mykonos"}
            itinerary.append(mykonos_stay)
            
            result = {"itinerary": itinerary}
            found_solution = True
            break
    
    if found_solution:
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()