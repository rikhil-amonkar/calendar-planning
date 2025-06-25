from z3 import *
import json

def main():
    city_names = ['Geneva', 'Istanbul', 'Venice', 'Vilnius', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Munich', 'Reykjavik']
    name_to_index = {name: idx for idx, name in enumerate(city_names)}
    index_to_name = {idx: name for name, idx in name_to_index.items()}
    
    req_days_arr = [4, 4, 5, 4, 4, 2, 2, 4, 5, 2]
    term_dict = {1: 3, 2: 4, 3: 3, 4: 3, 5: 1, 7: 3, 8: 4, 9: 1}
    
    flight_strs = [
        "Munich and Vienna", "Istanbul and Brussels", "Vienna and Vilnius", "Madrid and Munich", 
        "Venice and Brussels", "Riga and Brussels", "Geneva and Istanbul", "Munich and Reykjavik", 
        "Vienna and Istanbul", "Riga and Istanbul", "Reykjavik and Vienna", "Venice and Munich", 
        "Madrid and Venice", "Vilnius and Istanbul", "Venice and Vienna", "Venice and Istanbul", 
        "from Reykjavik to Madrid", "from Riga to Vilnius", "from Vilnius to Munich", "Madrid and Vienna", 
        "Vienna and Riga", "Geneva and Vienna", "Geneva and Brussels", "Geneva and Madrid", 
        "Munich and Brussels", "Madrid and Brussels", "Vienna and Brussels", "Geneva and Munich", 
        "Madrid and Istanbul"
    ]
    
    allowed_edges = set()
    for s in flight_strs:
        if s.startswith('from'):
            parts = s.split()
            city1 = parts[1]
            city2 = parts[3]
        else:
            parts = s.split(' and ')
            city1 = parts[0]
            city2 = parts[1]
        idx1 = name_to_index[city1]
        idx2 = name_to_index[city2]
        if idx1 > idx2:
            idx1, idx2 = idx2, idx1
        allowed_edges.add((idx1, idx2))
    
    middle_cities = [1, 2, 3, 4, 5, 7, 8, 9]
    
    s = Solver()
    n = 8
    order = [Int(f'c_{i}') for i in range(n)]
    
    for i in range(n):
        s.add(Or([order[i] == c for c in middle_cities]))
    s.add(Distinct(order))
    
    def connected(a, b):
        constraints = []
        for edge in allowed_edges:
            constraints.append(Or(
                And(a == edge[0], b == edge[1]),
                And(a == edge[1], b == edge[0])
            ))
        return Or(constraints)
    
    s.add(connected(0, order[0]))
    for i in range(n-1):
        s.add(connected(order[i], order[i+1]))
    s.add(connected(order[n-1], 6))
    
    cum = [Int(f'cum_{i}') for i in range(n+1)]
    s.add(cum[0] == 0)
    for i in range(n):
        term_i = If(order[i] == 1, 3,
                   If(order[i] == 2, 4,
                   If(order[i] == 3, 3,
                   If(order[i] == 4, 3,
                   If(order[i] == 5, 1,
                   If(order[i] == 7, 3,
                   If(order[i] == 8, 4,
                   If(order[i] == 9, 1, 0))))))))
        s.add(cum[i+1] == cum[i] + term_i)
    
    for i in range(n):
        s.add(If(order[i] == 2, cum[i] == 3, True))
        s.add(If(order[i] == 3, And(13 <= cum[i], cum[i] <= 19), True))
    
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n)]
        full_sequence = [0] + order_val + [6]
        
        a = [0] * 10
        d = [0] * 10
        a[0] = 1
        d[0] = a[0] + req_days_arr[full_sequence[0]] - 1
        for i in range(1, 10):
            a[i] = d[i-1]
            d[i] = a[i] + req_days_arr[full_sequence[i]] - 1
        
        itinerary = []
        for i in range(10):
            city_idx = full_sequence[i]
            city_name = index_to_name[city_idx]
            if a[i] == d[i]:
                day_range_str = f"Day {a[i]}"
            else:
                day_range_str = f"Day {a[i]}-{d[i]}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            if i < 9:
                itinerary.append({"day_range": f"Day {d[i]}", "place": city_name})
                next_city_name = index_to_name[full_sequence[i+1]]
                itinerary.append({"day_range": f"Day {d[i]}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()