from z3 import *
import json

def main():
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    days_req = [4, 5, 4, 3, 3, 4]
    allowed_pairs = [
        (0,4), (4,0),
        (4,1), (1,4),
        (1,3), (3,1),
        (0,5), (5,0),
        (2,0), (0,2),
        (5,4), (4,5)
    ]

    seq = [Int(f"seq_{i}") for i in range(6)]
    s = [Int(f"s_{i}") for i in range(6)]

    solver = Solver()

    for i in range(6):
        solver.add(And(seq[i] >= 0, seq[i] < 6))
    solver.add(Distinct(seq))

    for i in range(5):
        conds = []
        for pair in allowed_pairs:
            conds.append(And(seq[i] == pair[0], seq[i+1] == pair[1]))
        solver.add(Or(conds))

    def day(city):
        base = days_req[5]
        for idx in [4,3,2,1,0]:
            base = If(city == idx, days_req[idx], base)
        return base

    solver.add(s[0] == 1)
    for i in range(1, 6):
        solver.add(s[i] == s[i-1] + (day(seq[i-1]) - 1))

    porto_constraint = []
    for i in range(6):
        porto_constraint.append(And(seq[i] == 3, s[i] >= 14, s[i] <= 16))
    solver.add(Or(porto_constraint))

    if solver.check() == sat:
        model = solver.model()
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(6)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(6)]
        
        e_val = []
        for i in range(6):
            city_index = seq_val[i]
            end = s_val[i] + days_req[city_index] - 1
            e_val.append(end)
        
        itinerary_list = []
        for i in range(6):
            city_index = seq_val[i]
            city_name = cities[city_index]
            if s_val[i] == e_val[i]:
                day_range_str = f"Day {s_val[i]}"
            else:
                day_range_str = f"Day {s_val[i]}-{e_val[i]}"
            itinerary_list.append({"day_range": day_range_str, "place": city_name})
            
            if i < 5:
                itinerary_list.append({"day_range": f"Day {e_val[i]}", "place": city_name})
                next_city_index = seq_val[i+1]
                next_city_name = cities[next_city_index]
                itinerary_list.append({"day_range": f"Day {e_val[i]}", "place": next_city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()