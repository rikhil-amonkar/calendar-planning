from z3 import *
import json

def main():
    City, (dub, frank, krak) = EnumSort('City', ['Dubrovnik', 'Frankfurt', 'Krakow'])
    city_names = {
        dub: "Dubrovnik",
        frank: "Frankfurt",
        krak: "Krakow"
    }
    
    allowed_transitions = [
        (dub, dub), (dub, frank),
        (frank, frank), (frank, dub), (frank, krak),
        (krak, krak), (krak, frank)
    ]
    
    s0 = Const('s0', City)
    s = [Const(f's_{i}', City) for i in range(1, 11)]
    
    constraints = []
    
    constraints.append(Or([And(s0 == a, s[0] == b) for (a, b) in allowed_transitions]))
    
    for i in range(9):
        constraints.append(Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_transitions]))
    
    def count_city(start, end_list, C):
        total = 0
        total += If(start == C, 1, 0)
        total += If(And(start != end_list[0], end_list[0] == C), 1, 0)
        for idx in range(1, 10):
            start_day = end_list[idx-1]
            end_day = end_list[idx]
            total += If(start_day == C, 1, 0)
            total += If(And(start_day != end_day, end_day == C), 1, 0)
        return total
    
    total_dub = count_city(s0, s, dub)
    total_frank = count_city(s0, s, frank)
    total_krak = count_city(s0, s, krak)
    
    constraints.append(total_dub == 7)
    constraints.append(total_frank == 3)
    constraints.append(total_krak == 2)
    
    travel_days = 0
    travel_days += If(s0 != s[0], 1, 0)
    for i in range(9):
        travel_days += If(s[i] != s[i+1], 1, 0)
    constraints.append(travel_days == 2)
    
    constraints.append(Or(s[8] == krak, s[9] == krak))
    
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        s0_val = model[s0]
        s_vals = [model[s_i] for s_i in s]
        
        start_cities = [s0_val] + s_vals[:9]
        
        segments = []
        current_city = start_cities[0]
        start_day = 1
        for day in range(2, 11):
            idx = day - 1
            if start_cities[idx] is not current_city:
                end_day = day - 1
                segments.append((start_day, end_day, current_city))
                start_day = day
                current_city = start_cities[idx]
        segments.append((start_day, 10, current_city))
        
        itinerary = []
        for seg in segments:
            start, end, city_sym = seg
            city_name = city_names[city_sym]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({'day_range': day_range, 'place': city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()