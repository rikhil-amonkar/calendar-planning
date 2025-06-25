from z3 import *
import json

def main():
    city_names = ['Geneva', 'Istanbul', 'Venice', 'Vilnius', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Munich', 'Reykjavik']
    name_to_index = {name: idx for idx, name in enumerate(city_names)}
    index_to_name = {idx: name for name, idx in name_to_index.items()}
    
    req_days = {
        'Geneva': 4,
        'Istanbul': 4,
        'Venice': 5,
        'Vilnius': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    term_dict = {
        name_to_index['Istanbul']: 4,
        name_to_index['Venice']: 5,
        name_to_index['Vilnius']: 4,
        name_to_index['Vienna']: 4,
        name_to_index['Riga']: 2,
        name_to_index['Madrid']: 4,
        name_to_index['Munich']: 5,
        name_to_index['Reykjavik']: 2
    }
    
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
    
    middle_cities = [name_to_index[name] for name in ['Istanbul', 'Venice', 'Vilnius', 'Vienna', 'Riga', 'Madrid', 'Munich', 'Reykjavik']]
    
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
    
    s.add(connected(name_to_index['Geneva'], order[0]))
    for i in range(n-1):
        s.add(connected(order[i], order[i+1]))
    s.add(connected(order[n-1], name_to_index['Brussels']))
    
    cum = [Int(f'cum_{i}') for i in range(n+1)]
    s.add(cum[0] == 0)
    for i in range(n):
        term_i = term_dict[order[i]]
        s.add(cum[i+1] == cum[i] + term_i)
    s.add(cum[n] == 30)
    
    for i in range(n):
        s.add(If(order[i] == name_to_index['Venice'], cum[i] == 3 + i, True))
        s.add(If(order[i] == name_to_index['Vilnius'], cum[i] == 16 + i, True))
    
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n)]
        full_sequence = [name_to_index['Geneva']] + order_val + [name_to_index['Brussels']]
        
        a = [0] * 10
        d = [0] * 10
        a[0] = 1
        d[0] = a[0] + req_days[index_to_name[full_sequence[0]]] - 1
        for i in range(1, 10):
            a[i] = d[i-1]
            d[i] = a[i] + req_days[index_to_name[full_sequence[i]]] - 1
        
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