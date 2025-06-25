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
    for i in range(1, 7):
        prev_city_days = days_arr[p[i-1]]
        s.add(starts[i] == starts[i-1] + (prev_city_days - 1))
    
    lisbon_start = Int('lisbon_start')
    s.add(lisbon_start == If(p[0] == city_index["Lisbon"], starts[0],
                      If(p[1] == city_index["Lisbon"], starts[1],
                      If(p[2] == city_index["Lisbon"], starts[2],
                      If(p[3] == city_index["Lisbon"], starts[3],
                      If(p[4] == city_index["Lisbon"], starts[4],
                      If(p[5] == city_index["Lisbon"], starts[5],
                      starts[6]))))))
    s.add(lisbon_start >= 9, lisbon_start <= 13)
    
    oslo_start = Int('oslo_start')
    s.add(oslo_start == If(p[0] == city_index["Oslo"], starts[0],
                   If(p[1] == city_index["Oslo"], starts[1],
                   If(p[2] == city_index["Oslo"], starts[2],
                   If(p[3] == city_index["Oslo"], starts[3],
                   If(p[4] == city_index["Oslo"], starts[4],
                   If(p[5] == city_index["Oslo"], starts[5],
                   starts[6]))))))
    s.add(oslo_start >= 11, oslo_start <= 13)
    
    for i in range(6):
        constraints = []
        for edge in directed_edges:
            a, b = edge
            constraints.append(And(p[i] == a, p[i+1] == b))
        s.add(Or(constraints))
    
    last_city_end = starts[6] + (days_arr[p[6]] - 1)
    s.add(last_city_end == 15)
    
    if s.check() == sat:
        m = s.model()
        perm = [m.evaluate(p[i]).as_long() for i in range(7)]
        start_days = [1]
        for i in range(1, 7):
            prev_city_days = days_arr[perm[i-1]]
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