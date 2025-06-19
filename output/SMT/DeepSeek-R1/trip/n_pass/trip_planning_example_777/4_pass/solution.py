from z3 import *

def main():
    name_to_int = {
        'Dublin': 0,
        'Helsinki': 1,
        'Riga': 2,
        'Reykjavik': 3,
        'Vienna': 4,
        'Tallinn': 5
    }
    int_to_name = {v: k for k, v in name_to_int.items()}
    
    days_arr = [5, 3, 3, 2, 2, 5]
    
    edges_str = [
        "Helsinki and Riga",
        "Riga and Tallinn",
        "Vienna and Helsinki",
        "Riga and Dublin",
        "Vienna and Riga",
        "Reykjavik and Vienna",
        "Helsinki and Dublin",
        "Tallinn and Dublin",
        "Reykjavik and Helsinki",
        "Reykjavik and Dublin",
        "Helsinki and Tallinn",
        "Vienna and Dublin"
    ]
    allowed_edges = set()
    for e in edges_str:
        a, b = e.split(' and ')
        a_int = name_to_int[a]
        b_int = name_to_int[b]
        allowed_edges.add((a_int, b_int))
        allowed_edges.add((b_int, a_int))
    
    s = IntVector('s', 6)
    constraints = []
    
    for i in range(6):
        constraints.append(And(s[i] >= 0, s[i] < 6))
    
    constraints.append(Distinct(s))
    
    for i in range(5):
        constraints.append(Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_edges]))
    
    def get_day(city_expr):
        return If(city_expr == 0, 5,
              If(city_expr == 1, 3,
              If(city_expr == 2, 3,
              If(city_expr == 3, 2,
              If(city_expr == 4, 2, 5)))))
    
    a = IntVector('a', 6)
    constraints.append(a[0] == 1)
    for k in range(1, 6):
        sum_expr = Sum([get_day(s[i]) for i in range(k)])
        constraints.append(a[k] == 1 - k + sum_expr)
    
    for k in range(6):
        city_k = s[k]
        constraints.append(If(city_k == 4, And(a[k] >= 1, a[k] <= 3), True))  # Vienna event
        constraints.append(If(city_k == 5, And(a[k] >= 3, a[k] <= 11), True))  # Tallinn event
        constraints.append(If(city_k == 1, a[k] <= 5, True))  # Helsinki event
    
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s[i]).as_long() for i in range(6)]
        a_val = [model.evaluate(a[i]).as_long() for i in range(6)]
        
        end_val = []
        for i in range(6):
            city = s_val[i]
            dur = days_arr[city]
            end_val.append(a_val[i] + dur - 1)
        
        itinerary = []
        for i in range(6):
            city = s_val[i]
            city_name = int_to_name[city]
            start = a_val[i]
            end = end_val[i]
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
            if i < 5:
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
                next_city = s_val[i+1]
                next_city_name = int_to_name[next_city]
                itinerary.append({"day_range": f"Day {end}", "place": next_city_name})
        
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()