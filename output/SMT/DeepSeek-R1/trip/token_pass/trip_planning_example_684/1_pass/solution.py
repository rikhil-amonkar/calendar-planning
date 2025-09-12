import z3
import json

def main():
    n_days = 23
    n_stays = 6
    city_codes = ['AMS', 'EDI', 'BRU', 'VIE', 'BER', 'REK']
    city_days = [4, 5, 5, 5, 4, 5]
    
    direct_flights = [
        (1, 4), (0, 4), (1, 0), (3, 4), (4, 2),
        (3, 5), (1, 2), (3, 2), (0, 5), (5, 2),
        (0, 3), (5, 4)
    ]
    
    solver = z3.Solver()
    
    c = [z3.Int(f'c_{i}') for i in range(n_stays)]
    d = [z3.Int(f'd_{i}') for i in range(n_stays)]
    s = [z3.Int(f's_{i}') for i in range(n_stays)]
    e = [z3.Int(f'e_{i}') for i in range(n_stays)]
    
    solver.add(s[0] == 1)
    solver.add(e[5] == n_days)
    
    for i in range(n_stays):
        solver.add(e[i] == s[i] + d[i] - 1)
        for j in range(len(city_codes)):
            solver.add(z3.Implies(c[i] == j, d[i] == city_days[j]))
    
    for i in range(n_stays - 1):
        solver.add(s[i+1] == e[i])
    
    solver.add(z3.Distinct(c))
    for i in range(n_stays):
        solver.add(c[i] >= 0, c[i] <= 5)
    
    ams_constraint = z3.Or([z3.And(c[i] == 0, s[i] <= 5, e[i] >= 8) for i in range(n_stays)])
    solver.add(ams_constraint)
    
    ber_constraint = z3.Or([z3.And(c[i] == 4, s[i] <= 16, e[i] >= 19) for i in range(n_stays)])
    solver.add(ber_constraint)
    
    rek_constraint = z3.Or([z3.And(c[i] == 5, s[i] <= 12, e[i] >= 16) for i in range(n_stays)])
    solver.add(rek_constraint)
    
    for i in range(n_stays - 1):
        allowed = z3.Or([z3.And(c[i] == a, c[i+1] == b) for a, b in direct_flights] +
                        [z3.And(c[i] == b, c[i+1] == a) for a, b in direct_flights])
        solver.add(allowed)
    
    if solver.check() == z3.sat:
        model = solver.model()
        stay_cities = [model.evaluate(c[i]).as_long() for i in range(n_stays)]
        stay_starts = [model.evaluate(s[i]).as_long() for i in range(n_stays)]
        stay_ends = [model.evaluate(e[i]).as_long() for i in range(n_stays)]
        
        itinerary = []
        for i in range(n_stays):
            city_name = city_codes[stay_cities[i]]
            start_day = stay_starts[i]
            end_day = stay_ends[i]
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_name
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()