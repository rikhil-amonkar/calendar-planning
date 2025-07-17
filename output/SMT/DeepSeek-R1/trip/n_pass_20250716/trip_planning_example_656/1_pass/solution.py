from z3 import Solver, Int, Distinct, If, Sum, And, Or, sat
import json

def main():
    city_names = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
    days_map = {
        "Reykjavik": 5,
        "Istanbul": 4,
        "Edinburgh": 5,
        "Oslo": 2,
        "Stuttgart": 3,
        "Bucharest": 5
    }
    
    bidirectional_edges = [
        ("Bucharest", "Oslo"),
        ("Istanbul", "Oslo"),
        ("Bucharest", "Istanbul"),
        ("Stuttgart", "Edinburgh"),
        ("Istanbul", "Edinburgh"),
        ("Oslo", "Reykjavik"),
        ("Istanbul", "Stuttgart"),
        ("Oslo", "Edinburgh")
    ]
    
    directed_edges_list = []
    for (a, b) in bidirectional_edges:
        directed_edges_list.append((a, b))
        directed_edges_list.append((b, a))
    directed_edges_list.append(("Reykjavik", "Stuttgart"))
    
    s = Solver()
    pos = {}
    for city in city_names:
        pos[city] = Int(f'pos_{city}')
        s.add(pos[city] >= 0, pos[city] <= 5)
    
    s.add(Distinct([pos[city] for city in city_names]))
    
    start = {}
    for city in city_names:
        others = [other for other in city_names if other != city]
        start[city] = 1 + Sum([If(pos[other] < pos[city], days_map[other] - 1, 0) for other in others])
    
    ist_start = start["Istanbul"]
    ist_end = ist_start + days_map["Istanbul"] - 1
    s.add(ist_start <= 8, ist_end >= 5)
    
    osl_start = start["Oslo"]
    osl_end = osl_start + days_map["Oslo"] - 1
    s.add(osl_start <= 9, osl_end >= 8)
    
    for k in range(5):
        constraints = []
        for (A, B) in directed_edges_list:
            constraints.append(And(pos[A] == k, pos[B] == k+1))
        s.add(Or(constraints))
    
    if s.check() == sat:
        model = s.model()
        positions = {}
        for city in city_names:
            positions[city] = model.evaluate(pos[city]).as_long()
        
        sequence = sorted(city_names, key=lambda city: positions[city])
        
        current_day = 1
        stays = []
        for city in sequence:
            end_day = current_day + days_map[city] - 1
            stays.append((city, current_day, end_day))
            current_day = end_day
        
        itinerary = []
        for i, (city, start_day, end_day) in enumerate(stays):
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range_str, "place": city})
            
            if i < len(stays) - 1:
                itinerary.append({"day_range": f"Day {end_day}", "place": city})
                itinerary.append({"day_range": f"Day {end_day}", "place": stays[i+1][0]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()