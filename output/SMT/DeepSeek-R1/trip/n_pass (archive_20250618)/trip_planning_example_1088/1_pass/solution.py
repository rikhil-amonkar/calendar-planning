from z3 import *
import json

def main():
    cities = ["Reykjavik", "Stuttgart", "Split", "Geneva", "Porto", "Tallinn", "Oslo", "Stockholm"]
    n = len(cities)
    
    # Reduction: required_days - 1 for each city
    reduction = [1, 4, 2, 1, 2, 4, 4, 2]  # [Reykjavik, Stuttgart, Split, Geneva, Porto, Tallinn, Oslo, Stockholm]
    
    # Graph of direct flights (undirected)
    graph = {
        0: [1, 7, 5, 6],   # Reykjavik
        1: [0, 4, 7, 2],    # Stuttgart
        2: [6, 7, 1, 3],    # Split
        3: [6, 7, 4, 2],    # Geneva
        4: [1, 6, 3],       # Porto
        5: [0, 6],          # Tallinn
        6: [7, 0, 2, 3, 4, 5], # Oslo
        7: [0, 6, 1, 2, 3]  # Stockholm
    }
    
    s = Solver()
    
    # City assignment for 8 segments
    city_vars = [Int(f'city_{i}') for i in range(n)]
    
    # Constraints: city0 is Reykjavik (0), city7 is Porto (4)
    s.add(city_vars[0] == 0)
    s.add(city_vars[7] == 4)
    
    # All cities are distinct
    s.add(Distinct(city_vars))
    
    # Flight constraints between consecutive segments
    for i in range(7):
        current = city_vars[i]
        next_city = city_vars[i+1]
        conds = []
        for idx in range(n):
            allowed_next = graph[idx]
            conds.append(And(current == idx, Or([next_city == j for j in allowed_next])))
        s.add(Or(conds))
    
    # Cumulative reduction array (cum[0..8])
    cum = [Int(f'cum_{i}') for i in range(n+1)]
    s.add(cum[0] == 0)
    for i in range(1, n+1):
        expr = cum[i-1]
        for j in range(n):
            expr = If(city_vars[i-1] == j, expr + reduction[j], expr)
        s.add(cum[i] == expr)
    
    # Constraint for Stockholm (index 7): must start by day 4
    for i in range(n):
        s.add(If(city_vars[i] == 7, cum[i] <= 3, True))
    
    # Total reduction must be 20
    s.add(cum[8] == 20)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        city_val = [m.eval(city_vars[i]).as_long() for i in range(n)]
        cum_val = [0] * (n+1)
        cum_val[0] = 0
        for i in range(1, n+1):
            cum_val[i] = cum_val[i-1] + reduction[city_val[i-1]]
        
        start_days = [1 + cum_val[i] for i in range(n)]
        end_days = [start_days[i] + reduction[city_val[i]] for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_name = cities[city_val[i]]
            start = start_days[i]
            end = end_days[i]
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city_name
            })
            if i < n-1:  # not the last segment
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": city_name
                })
                next_city_name = cities[city_val[i+1]]
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": next_city_name
                })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()