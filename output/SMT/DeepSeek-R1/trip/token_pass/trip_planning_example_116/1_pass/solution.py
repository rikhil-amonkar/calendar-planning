from z3 import *
import json

def main():
    n_days = 18
    cities = ['Split', 'Santorini', 'London']
    
    in_dict = {}
    for i in range(1, n_days + 1):
        for c in cities:
            in_dict[(i, c)] = Bool(f"in_{i}_{c}")
    
    s = Solver()
    
    flight_days_count = 0
    for i in range(1, n_days + 1):
        cities_today = [in_dict[(i, c)] for c in cities]
        s.add(Or(cities_today))
        s.add(AtMost(*cities_today, 2))
        count = Sum([If(in_dict[(i, c)], 1, 0) for c in cities])
        flight_days_count += If(count == 2, 1, 0)
    
    s.add(flight_days_count == 2)
    
    city_totals = [('Split', 6), ('Santorini', 7), ('London', 7)]
    for c, total in city_totals:
        s.add(Sum([If(in_dict[(i, c)], 1, 0) for i in range(1, n_days + 1)]) == total)
    
    allowed_pairs = [('London', 'Santorini'), ('Split', 'London')]
    for i in range(1, n_days + 1):
        for c1 in cities:
            for c2 in cities:
                if c1 < c2 and (c1, c2) not in allowed_pairs and (c2, c1) not in allowed_pairs:
                    s.add(Not(And(in_dict[(i, c1)], in_dict[(i, c2)])))
    
    s.add(in_dict[(12, 'Santorini')])
    s.add(in_dict[(18, 'Santorini')])
    
    if s.check() == sat:
        m = s.model()
        flight_days = []
        for i in range(1, n_days + 1):
            count = sum(1 for c in cities if m.evaluate(in_dict[(i, c)]))
            if count == 2:
                flight_days.append(i)
        flight_days.sort()
        d1, d2 = flight_days[0], flight_days[1]
        
        city1 = next(c for c in cities if m.evaluate(in_dict[(1, c)]))
        city2 = next(c for c in cities if c != city1 and m.evaluate(in_dict[(d1, c)]))
        city3 = next(c for c in cities if c != city2 and m.evaluate(in_dict[(d2, c)]))
        
        itinerary = [
            {"day_range": f"Day 1-{d1}", "place": city1},
            {"day_range": f"Day {d1}-{d2}", "place": city2},
            {"day_range": f"Day {d2}-{n_days}", "place": city3}
        ]
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()