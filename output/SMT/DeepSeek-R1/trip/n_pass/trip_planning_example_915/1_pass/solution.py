from z3 import *
import json

def main():
    # City labels
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    city_to_id = {name: idx for idx, name in enumerate(cities)}
    id_to_city = {idx: name for idx, name in enumerate(cities)}
    
    # Required days per city
    req_days = {
        city_to_id["Bucharest"]: 3,
        city_to_id["Venice"]: 5,
        city_to_id["Prague"]: 4,
        city_to_id["Frankfurt"]: 5,
        city_to_id["Zurich"]: 5,
        city_to_id["Florence"]: 5,
        city_to_id["Tallinn"]: 5
    }
    
    # Directed flight edges: (from, to)
    edges = [
        (city_to_id["Prague"], city_to_id["Tallinn"]),
        (city_to_id["Tallinn"], city_to_id["Prague"]),
        (city_to_id["Prague"], city_to_id["Zurich"]),
        (city_to_id["Zurich"], city_to_id["Prague"]),
        (city_to_id["Florence"], city_to_id["Prague"]),
        (city_to_id["Prague"], city_to_id["Florence"]),
        (city_to_id["Frankfurt"], city_to_id["Bucharest"]),
        (city_to_id["Bucharest"], city_to_id["Frankfurt"]),
        (city_to_id["Frankfurt"], city_to_id["Venice"]),
        (city_to_id["Venice"], city_to_id["Frankfurt"]),
        (city_to_id["Prague"], city_to_id["Bucharest"]),
        (city_to_id["Bucharest"], city_to_id["Prague"]),
        (city_to_id["Bucharest"], city_to_id["Zurich"]),
        (city_to_id["Zurich"], city_to_id["Bucharest"]),
        (city_to_id["Tallinn"], city_to_id["Frankfurt"]),
        (city_to_id["Frankfurt"], city_to_id["Tallinn"]),
        (city_to_id["Zurich"], city_to_id["Florence"]),  # Only Zurich to Florence
        (city_to_id["Frankfurt"], city_to_id["Zurich"]),
        (city_to_id["Zurich"], city_to_id["Frankfurt"]),
        (city_to_id["Zurich"], city_to_id["Venice"]),
        (city_to_id["Venice"], city_to_id["Zurich"]),
        (city_to_id["Florence"], city_to_id["Frankfurt"]),
        (city_to_id["Frankfurt"], city_to_id["Florence"]),
        (city_to_id["Prague"], city_to_id["Frankfurt"]),
        (city_to_id["Frankfurt"], city_to_id["Prague"]),
        (city_to_id["Tallinn"], city_to_id["Zurich"]),
        (city_to_id["Zurich"], city_to_id["Tallinn"])
    ]
    
    # Create Z3 variables
    order = [Int('o%d' % i) for i in range(7)]
    d0, d1, d2, d3, d4, d5 = Ints('d0 d1 d2 d3 d4 d5')
    d = [d0, d1, d2, d3, d4, d5]  # Travel days
    
    s = Solver()
    
    # Domain constraints for order: each between 0 and 6
    for i in range(7):
        s.add(order[i] >= 0, order[i] <= 6)
    s.add(Distinct(order))
    
    # Travel day constraints: strictly increasing and within [1, 26]
    s.add(d0 >= 1, d5 <= 26)
    for i in range(5):
        s.add(d[i] < d[i+1])
    
    # Stay duration constraints
    s.add(d0 == req_days[order[0]])
    for i in range(1, 6):
        s.add(d[i] - d[i-1] + 1 == req_days[order[i]])
    s.add(27 - d5 == req_days[order[6]])
    
    # Event constraints
    # Venice (city_to_id["Venice"] = 1)
    for j in range(7):
        if j == 0:
            s.add(Implies(order[0] == 1, d0 >= 22))
        elif j == 6:
            pass  # Automatically satisfied
        else:
            s.add(Implies(order[j] == 1, And(d[j-1] <= 26, d[j] >= 22)))
    
    # Frankfurt (city_to_id["Frankfurt"] = 3)
    for j in range(7):
        if j == 0:
            s.add(Implies(order[0] == 3, d0 >= 12))
        elif j == 6:
            s.add(Implies(order[6] == 3, d5 <= 16))
        else:
            s.add(Implies(order[j] == 3, And(d[j-1] <= 16, d[j] >= 12)))
    
    # Tallinn (city_to_id["Tallinn"] = 6)
    for j in range(7):
        if j == 0:
            s.add(Implies(order[0] == 6, d0 >= 8))
        elif j == 6:
            s.add(Implies(order[6] == 6, d5 <= 12))
        else:
            s.add(Implies(order[j] == 6, And(d[j-1] <= 12, d[j] >= 8)))
    
    # Flight constraints
    for j in range(6):
        s.add(Or([And(order[j] == a, order[j+1] == b) for (a, b) in edges]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        order_vals = [m[order[i]].as_long() for i in range(7)]
        d_vals = [m[d[i]].as_long() for i in range(6)]
        
        itinerary = []
        # First city
        c0 = order_vals[0]
        start0 = 1
        end0 = d_vals[0]
        itinerary.append({"day_range": "Day %d-%d" % (start0, end0), "place": id_to_city[c0]})
        itinerary.append({"day_range": "Day %d" % end0, "place": id_to_city[c0]})
        c1 = order_vals[1]
        itinerary.append({"day_range": "Day %d" % end0, "place": id_to_city[c1]})
        
        # Cities 1 to 5
        for i in range(1, 6):
            c = order_vals[i]
            start_i = d_vals[i-1]
            end_i = d_vals[i]
            itinerary.append({"day_range": "Day %d-%d" % (start_i, end_i), "place": id_to_city[c]})
            itinerary.append({"day_range": "Day %d" % end_i, "place": id_to_city[c]})
            c_next = order_vals[i+1]
            itinerary.append({"day_range": "Day %d" % end_i, "place": id_to_city[c_next]})
        
        # Last city (index 6)
        c6 = order_vals[6]
        start6 = d_vals[5]
        itinerary.append({"day_range": "Day %d-26" % start6, "place": id_to_city[c6]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()