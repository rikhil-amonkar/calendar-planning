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
    
    req_days_list = [0] * 10
    for city, days in req_days.items():
        idx = name_to_index[city]
        req_days_list[idx] = days
    
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
    
    full_sequence = [Int(f'city_{i}') for i in range(10)]
    s.add(full_sequence[0] == name_to_index['Geneva'])
    s.add(full_sequence[9] == name_to_index['Brussels'])
    
    for i in range(1, 9):
        s.add(Or([full_sequence[i] == c for c in middle_cities]))
    s.add(Distinct([full_sequence[i] for i in range(1, 9)]))
    
    req_days_array = Array('req_days', IntSort(), IntSort())
    for idx in range(10):
        req_days_array = Store(req_days_array, idx, req_days_list[idx])
    
    a = [Int(f'a_{i}') for i in range(10)]
    d = [Int(f'd_{i}') for i in range(10)]
    
    s.add(a[0] == 1)
    s.add(d[0] == a[0] + Select(req_days_array, full_sequence[0]) - 1)
    
    for i in range(1, 10):
        s.add(a[i] == d[i-1])
        s.add(d[i] == a[i] + Select(req_days_array, full_sequence[i]) - 1)
    s.add(d[9] == 27)
    
    venice_idx = name_to_index['Venice']
    vilnius_idx = name_to_index['Vilnius']
    for i in range(10):
        s.add(If(full_sequence[i] == venice_idx, And(a[i] == 7, d[i] == 11), True))
        s.add(If(full_sequence[i] == vilnius_idx, And(a[i] == 20, d[i] == 23), True))
    
    for i in range(9):
        city1 = full_sequence[i]
        city2 = full_sequence[i+1]
        edge_exists = Or()
        for edge in allowed_edges:
            edge_exists = Or(edge_exists, 
                             And(city1 == edge[0], city2 == edge[1]),
                             And(city1 == edge[1], city2 == edge[0]))
        s.add(edge_exists)
    
    if s.check() == sat:
        model = s.model()
        seq_val = [model.evaluate(full_sequence[i]).as_long() for i in range(10)]
        a_val = [model.evaluate(a[i]).as_long() for i in range(10)]
        d_val = [model.evaluate(d[i]).as_long() for i in range(10)]
        
        itinerary = []
        for i in range(10):
            city_idx = seq_val[i]
            city_name = index_to_name[city_idx]
            if a_val[i] == d_val[i]:
                day_range_str = f"Day {a_val[i]}"
            else:
                day_range_str = f"Day {a_val[i]}-{d_val[i]}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            if i < 9:
                itinerary.append({"day_range": f"Day {d_val[i]}", "place": city_name})
                next_city_name = index_to_name[seq_val[i+1]]
                itinerary.append({"day_range": f"Day {d_val[i]}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()