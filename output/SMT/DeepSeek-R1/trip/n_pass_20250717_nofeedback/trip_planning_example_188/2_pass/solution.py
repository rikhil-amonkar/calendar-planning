from z3 import *
import json

def main():
    city_names = {
        0: "Brussels",
        1: "Barcelona",
        2: "Split"
    }
    
    n_days = 12
    n_flights = n_days - 1

    L = [Int('L_%d' % i) for i in range(n_days)]
    F = [Bool('F_%d' % i) for i in range(n_flights)]
    
    s = Solver()
    
    s.add(L[0] == 0)
    s.add(F[0] == False)
    
    for i in range(n_flights):
        s.add(If(F[i],
                 Or(
                     And(L[i] == 0, L[i+1] == 1),
                     And(L[i] == 1, L[i+1] == 0),
                     And(L[i] == 1, L[i+1] == 2),
                     And(L[i] == 2, L[i+1] == 1)
                 ),
                 L[i+1] == L[i]
                ))
    
    for i in range(n_days):
        s.add(Or(L[i] == 0, L[i] == 1, L[i] == 2))
    
    days_B = 0
    days_A = 0
    days_S = 0
    
    for j in range(n_days):
        if j < n_flights:
            in_B = Or(L[j] == 0, And(F[j], L[j+1] == 0))
            in_A = Or(L[j] == 1, And(F[j], L[j+1] == 1))
            in_S = Or(L[j] == 2, And(F[j], L[j+1] == 2))
        else:
            in_B = (L[j] == 0)
            in_A = (L[j] == 1)
            in_S = (L[j] == 2)
        
        days_B += If(in_B, 1, 0)
        days_A += If(in_A, 1, 0)
        days_S += If(in_S, 1, 0)
    
    s.add(days_B == 2)
    s.add(days_A == 7)
    s.add(days_S == 5)
    
    if s.check() == sat:
        m = s.model()
        L_val = [m.evaluate(L[i]).as_long() for i in range(n_days)]
        F_val = [is_true(m.evaluate(F[i])) for i in range(n_flights)]
        
        city_days = {
            "Brussels": set(),
            "Barcelona": set(),
            "Split": set()
        }
        
        for d in range(1, n_days+1):
            idx = d - 1
            cities_today = set()
            cities_today.add(L_val[idx])
            if d < n_days and F_val[idx]:
                cities_today.add(L_val[idx+1])
            for c_code in cities_today:
                city_name = city_names[c_code]
                city_days[city_name].add(d)
                
        blocks = []
        for city, days_set in city_days.items():
            if not days_set:
                continue
            days_list = sorted(days_set)
            start = days_list[0]
            last = start
            for i in range(1, len(days_list)):
                if days_list[i] == last + 1:
                    last = days_list[i]
                else:
                    blocks.append((start, last, city))
                    start = days_list[i]
                    last = start
            blocks.append((start, last, city))
        
        blocks_sorted = sorted(blocks, key=lambda x: (x[0], x[2]))
        
        itinerary_list = []
        for (start, end, city) in blocks_sorted:
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()