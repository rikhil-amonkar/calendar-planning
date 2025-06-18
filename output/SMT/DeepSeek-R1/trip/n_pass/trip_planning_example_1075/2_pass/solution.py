from z3 import *
import json

def main():
    city_names = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    days_arr = [4, 3, 4, 5, 5, 2, 5, 4]
    index_dict = {city: idx for idx, city in enumerate(city_names)}
    
    flight_strings = [
        "from Reykjavik to Stuttgart",
        "Stuttgart and Split",
        "Stuttgart and Vienna",
        "Prague and Manchester",
        "Edinburgh and Prague",
        "from Manchester to Split",
        "Prague and Vienna",
        "Vienna and Manchester",
        "Prague and Split",
        "Vienna and Lyon",
        "Stuttgart and Edinburgh",
        "Split and Lyon",
        "Stuttgart and Manchester",
        "Prague and Lyon",
        "Reykjavik and Vienna",
        "Prague and Reykjavik",
        "Vienna and Split"
    ]
    
    directed_edges = set()
    for s in flight_strings:
        if s.startswith("from"):
            parts = s.split()
            A = parts[1]
            B = parts[3]
            directed_edges.add((A, B))
        else:
            parts = s.split(' and ')
            A = parts[0].strip()
            B = parts[1].strip()
            directed_edges.add((A, B))
            directed_edges.add((B, A))
    
    directed_index_edges = set()
    for (A, B) in directed_edges:
        iA = index_dict[A]
        iB = index_dict[B]
        directed_index_edges.add((iA, iB))
    
    order = [Int(f"order_{i}") for i in range(8)]
    
    constraints = [Distinct(order)]
    for i in range(8):
        constraints.append(And(order[i] >= 0, order[i] < 8))
    
    for i in range(7):
        options = []
        for (a, b) in directed_index_edges:
            options.append(And(order[i] == a, order[i+1] == b))
        constraints.append(Or(options))
    
    S = [Int(f"S_{i}") for i in range(9)]
    constraints.append(S[0] == 0)
    for i in range(1, 9):
        day_expr = Int(f"day_{i-1}")
        options = []
        for idx in range(8):
            options.append(And(order[i-1] == idx, day_expr == days_arr[idx]))
        constraints.append(Or(options))
        constraints.append(S[i] == S[i-1] + day_expr)
    
    edinburgh_cons = Or([And(order[k] == index_dict["Edinburgh"], S[k] - k == 4) for k in range(8)])
    constraints.append(edinburgh_cons)
    
    split_cons = Or([And(order[k] == index_dict["Split"], S[k] - k == 18) for k in range(8)])
    constraints.append(split_cons)
    
    s = Solver()
    s.add(constraints)
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]) for i in range(8)]
        order_indices = [val.as_long() for val in order_vals]
        prefix = [0] * 9
        for i in range(1, 9):
            city_idx = order_indices[i-1]
            prefix[i] = prefix[i-1] + days_arr[city_idx]
        
        itinerary = []
        s0 = 1
        d0 = days_arr[order_indices[0]]
        e0 = s0 + d0 - 1
        city0 = city_names[order_indices[0]]
        itinerary.append({"day_range": f"Day {s0}-{e0}", "place": city0})
        if 0 < 7:
            itinerary.append({"day_range": f"Day {e0}", "place": city0})
        
        for i in range(1, 7):
            s_i = 1 + prefix[i] - i
            d_i = days_arr[order_indices[i]]
            e_i = s_i + d_i - 1
            city_i = city_names[order_indices[i]]
            itinerary.append({"day_range": f"Day {s_i}", "place": city_i})
            itinerary.append({"day_range": f"Day {s_i}-{e_i}", "place": city_i})
            if i < 7:
                itinerary.append({"day_range": f"Day {e_i}", "place": city_i})
        
        i = 7
        s_i = 1 + prefix[i] - i
        d_i = days_arr[order_indices[i]]
        e_i = s_i + d_i - 1
        city_i = city_names[order_indices[i]]
        itinerary.append({"day_range": f"Day {s_i}", "place": city_i})
        itinerary.append({"day_range": f"Day {s_i}-{e_i}", "place": city_i})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()