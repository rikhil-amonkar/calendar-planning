from z3 import *
import json

def main():
    cities = ["Porto", "Amsterdam", "Helsinki", "Naples", "Brussels", "Split", "Reykjavik", "Lyon", "Warsaw", "Valencia"]
    durations = [5, 4, 4, 4, 3, 3, 5, 3, 3, 2]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    direct_flights = [
        "Amsterdam and Warsaw",
        "Helsinki and Brussels",
        "Helsinki and Warsaw",
        "Reykjavik and Brussels",
        "Amsterdam and Lyon",
        "Amsterdam and Naples",
        "Amsterdam and Reykjavik",
        "Naples and Valencia",
        "Porto and Brussels",
        "Amsterdam and Split",
        "Lyon and Split",
        "Warsaw and Split",
        "Porto and Amsterdam",
        "Helsinki and Split",
        "Brussels and Lyon",
        "Porto and Lyon",
        "Reykjavik and Warsaw",
        "Brussels and Valencia",
        "Valencia and Lyon",
        "Porto and Warsaw",
        "Warsaw and Valencia",
        "Amsterdam and Helsinki",
        "Porto and Valencia",
        "Warsaw and Brussels",
        "Warsaw and Naples",
        "Naples and Split",
        "Helsinki and Naples",
        "Helsinki and Reykjavik",
        "Amsterdam and Valencia",
        "Naples and Brussels"
    ]
    
    edge_set = set()
    for flight in direct_flights:
        parts = flight.split(' and ')
        city1 = parts[0].strip()
        city2 = parts[1].strip()
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        edge_set.add((idx1, idx2))
        edge_set.add((idx2, idx1))
    
    s = [Int(f's_{i}') for i in range(10)]
    e = [Int(f'e_{i}') for i in range(10)]
    order = [Int(f'order_{i}') for i in range(10)]
    
    solver = Solver()
    
    for i in range(10):
        solver.add(order[i] >= 0, order[i] < 10)
    solver.add(Distinct(order))
    
    d = durations
    
    start_val = 1
    for i in range(10):
        idx = order[i]
        solver.add(s[idx] == start_val)
        solver.add(e[idx] == start_val + d[idx] - 1)
        start_val = e[idx]
    
    solver.add(s[city_index["Porto"]] <= 5)
    
    amsterdam_idx = city_index["Amsterdam"]
    solver.add(s[amsterdam_idx] <= 8)
    solver.add(e[amsterdam_idx] >= 5)
    
    helsinki_idx = city_index["Helsinki"]
    solver.add(s[helsinki_idx] <= 11)
    solver.add(e[helsinki_idx] >= 8)
    
    naples_idx = city_index["Naples"]
    solver.add(s[naples_idx] <= 20)
    solver.add(e[naples_idx] >= 17)
    
    brussels_idx = city_index["Brussels"]
    solver.add(s[brussels_idx] <= 22)
    solver.add(e[brussels_idx] >= 20)
    
    for i in range(9):
        edge_conds = []
        for (a, b) in edge_set:
            edge_conds.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(edge_conds))
    
    if solver.check() == sat:
        model = solver.model()
        order_vals = [model[order[i]].as_long() for i in range(10)]
        s_vals = [model[s[i]].as_long() for i in range(10)]
        e_vals = [model[e[i]].as_long() for i in range(10)]
        
        itinerary = []
        for i in range(10):
            city = cities[order_vals[i]]
            start_day = s_vals[order_vals[i]]
            end_day = e_vals[order_vals[i]]
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            if i < 9:
                next_city = cities[order_vals[i+1]]
                itinerary.append({"day_range": f"Day {end_day}", "place": city})
                itinerary.append({"day_range": f"Day {end_day}", "place": next_city})
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()