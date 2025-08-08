from z3 import *

def main():
    cities = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
    city_dict = {c: idx for idx, c in enumerate(cities)}
    
    edges_str = [
        ("Hamburg", "Frankfurt"),
        ("Naples", "Mykonos"),
        ("Hamburg", "Porto"),
        ("Hamburg", "Geneva"),
        ("Mykonos", "Geneva"),
        ("Frankfurt", "Geneva"),
        ("Frankfurt", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Manchester"),
        ("Naples", "Manchester"),
        ("Frankfurt", "Naples"),
        ("Frankfurt", "Manchester"),
        ("Naples", "Geneva"),
        ("Porto", "Manchester"),
        ("Hamburg", "Manchester")
    ]
    
    allowed_pairs_set_str = set()
    for a, b in edges_str:
        allowed_pairs_set_str.add((a, b))
        allowed_pairs_set_str.add((b, a))
    allowed_pairs_int = [(city_dict[a], city_dict[b]) for a, b in allowed_pairs_set_str]
    
    L = [Int(f'L_{i}') for i in range(18)]
    s = Solver()
    
    for i in range(18):
        s.add(Or([L[i] == idx for idx in range(7)]))
    
    for i in range(1, 18):
        conds = [And(L[i-1] == a, L[i] == b) for (a, b) in allowed_pairs_int]
        s.add(Or(L[i] == L[i-1], Or(conds)))
    
    total_days = {c: 0 for c in cities}
    for c in cities:
        idx = city_dict[c]
        total = If(L[0] == idx, 1, 0)
        for i in range(1, 18):
            total += If(Or(L[i-1] == idx, L[i] == idx), 1, 0)
        total_days[c] = total
        
    s.add(total_days["Porto"] == 2)
    s.add(total_days["Geneva"] == 3)
    s.add(total_days["Mykonos"] == 3)
    s.add(total_days["Manchester"] == 4)
    s.add(total_days["Hamburg"] == 5)
    s.add(total_days["Naples"] == 5)
    s.add(total_days["Frankfurt"] == 2)
    
    mykonos_idx = city_dict["Mykonos"]
    s.add(Or(
        Or(L[8] == mykonos_idx, L[9] == mykonos_idx),
        Or(L[9] == mykonos_idx, L[10] == mykonos_idx),
        Or(L[10] == mykonos_idx, L[11] == mykonos_idx)
    ))
    
    manchester_idx = city_dict["Manchester"]
    s.add(Or(
        Or(L[13] == manchester_idx, L[14] == manchester_idx),
        Or(L[14] == manchester_idx, L[15] == manchester_idx),
        Or(L[15] == manchester_idx, L[16] == manchester_idx),
        Or(L[16] == manchester_idx, L[17] == manchester_idx)
    ))
    
    frankfurt_idx = city_dict["Frankfurt"]
    s.add(Or(L[3] == frankfurt_idx, L[4] == frankfurt_idx))
    s.add(Or(L[4] == frankfurt_idx, L[5] == frankfurt_idx))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 19):
            idx = day - 1
            city_index = model[L[idx]].as_long()
            city_name = cities[city_index]
            itinerary.append({"day": day, "city": city_name})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()