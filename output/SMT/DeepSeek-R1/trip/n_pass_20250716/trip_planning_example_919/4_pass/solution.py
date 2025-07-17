from z3 import *

def main():
    city_names = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    city_index = {name: idx for idx, name in enumerate(city_names)}
    days_arr = [4, 2, 3, 2, 3, 4, 3]  # days required for each city

    bidirectional_pairs = [
        ("Riga", "Oslo"),
        ("Rome", "Oslo"),
        ("Vienna", "Milan"),
        ("Vienna", "Vilnius"),
        ("Vienna", "Lisbon"),
        ("Riga", "Milan"),
        ("Lisbon", "Oslo"),
        ("Rome", "Lisbon"),
        ("Vienna", "Riga"),
        ("Vienna", "Rome"),
        ("Milan", "Oslo"),
        ("Vienna", "Oslo"),
        ("Vilnius", "Oslo"),
        ("Vilnius", "Milan"),
        ("Riga", "Lisbon")
    ]
    unidirectional_pairs = [
        ("Rome", "Riga"),
        ("Riga", "Vilnius")
    ]
    
    directed_edges = set()
    for a, b in bidirectional_pairs:
        i = city_index[a]
        j = city_index[b]
        directed_edges.add((i, j))
        directed_edges.add((j, i))
    for a, b in unidirectional_pairs:
        i = city_index[a]
        j = city_index[b]
        directed_edges.add((i, j))
    
    p = [Int(f'p_{i}') for i in range(7)]
    s = Solver()
    
    for i in range(7):
        s.add(p[i] >= 0, p[i] < 7)
    s.add(Distinct(p))
    s.add(p[0] == city_index["Vienna"])
    
    starts = [Int(f'start_{i}') for i in range(7)]
    s.add(starts[0] == 1)
    
    def city_days_expr(city_var):
        expr = days_arr[0]
        for idx in range(1, 7):
            expr = If(city_var == idx, days_arr[idx], expr)
        return expr
    
    for i in range(1, 7):
        prev_city_days = city_days_expr(p[i-1])
        s.add(starts[i] == starts[i-1] + (prev_city_days - 1))
    
    lisbon_start = Int('lisbon_start')
    expr_lisbon = starts[6]
    for i in range(5, -1, -1):
        expr_lisbon = If(p[i] == city_index["Lisbon"], starts[i], expr_lisbon)
    s.add(lisbon_start == expr_lisbon)
    s.add(lisbon_start == 11)  # Fixed start day for Lisbon
    
    oslo_start = Int('oslo_start')
    expr_oslo = starts[6]
    for i in range(5, -1, -1):
        expr_oslo = If(p[i] == city_index["Oslo"], starts[i], expr_oslo)
    s.add(oslo_start == expr_oslo)
    s.add(oslo_start == 13)  # Fixed start day for Oslo
    
    for i in range(6):
        constraints = []
        for edge in directed_edges:
            a, b = edge
            constraints.append(And(p[i] == a, p[i+1] == b))
        s.add(Or(constraints))
    
    last_city_end = starts[6] + (city_days_expr(p[6]) - 1)
    s.add(last_city_end == 15)
    
    if s.check() == sat:
        m = s.model()
        perm = [m.evaluate(p[i]).as_long() for i in range(7)]
        start_days = [1]
        for i in range(1, 7):
            prev_city_idx = perm[i-1]
            prev_city_days = days_arr[prev_city_idx]
            start_days.append(start_days[i-1] + (prev_city_days - 1))
        
        itinerary = []
        for i in range(7):
            city_idx = perm[i]
            start = start_days[i]
            duration = days_arr[city_idx]
            end = start + duration - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_names[city_idx]})
            if i < 6:
                itinerary.append({"day_range": f"Day {end}", "place": city_names[city_idx]})
                next_city_idx = perm[i+1]
                itinerary.append({"day_range": f"Day {end}", "place": city_names[next_city_idx]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()