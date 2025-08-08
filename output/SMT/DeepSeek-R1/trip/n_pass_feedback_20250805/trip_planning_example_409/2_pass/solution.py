from z3 import *
import json

def main():
    cities = ["Zurich", "Hamburg", "Helsinki", "Bucharest", "Split"]
    city_to_int = {name: idx for idx, name in enumerate(cities)}
    
    undirected_edges = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg")
    ]
    
    directed_edges = []
    for u, v in undirected_edges:
        u_idx = city_to_int[u]
        v_idx = city_to_int[v]
        directed_edges.append((u_idx, v_idx))
        directed_edges.append((v_idx, u_idx))
    
    required_days = [3, 2, 2, 2, 7]
    zurich = city_to_int["Zurich"]
    split = city_to_int["Split"]
    
    s = Solver()
    
    # Start city of day 1
    S0 = Int('S0')
    s.add(S0 >= 0, S0 < 5)
    
    # End cities for each day (day1 to day12)
    L = [Int(f'L_{i}') for i in range(12)]
    for i in range(12):
        s.add(L[i] >= 0, L[i] < 5)
    
    # Flight constraints for day1
    s.add(If(S0 != L[0], 
             Or([And(S0 == u, L[0] == v) for (u, v) in directed_edges]),
             True))
    
    # Flight constraints for day2 to day12
    for i in range(1, 12):
        s.add(If(L[i-1] != L[i],
                 Or([And(L[i-1] == u, L[i] == v) for (u, v) in directed_edges]),
                 True))
    
    # Wedding constraint: must be in Zurich on at least one of days 1, 2, or 3
    s.add(Or(S0 == zurich, L[0] == zurich, L[1] == zurich, L[2] == zurich))
    
    # Conference constraints: must be in Split on day4 and day10
    s.add(Or(L[2] == split, L[3] == split))  # Day4
    s.add(Or(L[8] == split, L[9] == split))   # Day10
    
    # Total days constraints for each city
    for c in range(5):
        base_count = Sum([If(L[i] == c, 1, 0) for i in range(12)])
        start_leave1 = If(And(S0 == c, L[0] != c), 1, 0)
        other_leaves = Sum([If(And(L[i-1] == c, L[i] != c), 1, 0) for i in range(1, 12)])
        total_days = base_count + start_leave1 + other_leaves
        s.add(total_days == required_days[c])
    
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for i in range(12):
            city_idx = model.evaluate(L[i]).as_long()
            city_name = cities[city_idx]
            itinerary_list.append({"day": i+1, "place": city_name})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()