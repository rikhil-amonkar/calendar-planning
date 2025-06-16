from z3 import *

def main():
    city_map = {
        'Venice': 0,
        'Barcelona': 1,
        'Copenhagen': 2,
        'Lyon': 3,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 6,
        'Tallinn': 7,
        'Munich': 8
    }
    
    reverse_city_map = {v: k for k, v in city_map.items()}
    
    durations = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    
    connections = [
        "Copenhagen and Athens",
        "Copenhagen and Dubrovnik",
        "Munich and Tallinn",
        "Copenhagen and Munich",
        "Venice and Munich",
        "from Reykjavik to Athens",
        "Athens and Dubrovnik",
        "Venice and Athens",
        "Lyon and Barcelona",
        "Copenhagen and Reykjavik",
        "Reykjavik and Munich",
        "Athens and Munich",
        "Lyon and Munich",
        "Barcelona and Reykjavik",
        "Venice and Copenhagen",
        "Barcelona and Dubrovnik",
        "Lyon and Venice",
        "Dubrovnik and Munich",
        "Barcelona and Athens",
        "Copenhagen and Barcelona",
        "Venice and Barcelona",
        "Barcelona and Munich",
        "Barcelona and Tallinn",
        "Copenhagen and Tallinn"
    ]
    
    directed_edges = set()
    for conn in connections:
        if conn.startswith('from'):
            parts = conn.split()
            if len(parts) == 4:
                from_city = parts[1]
                to_city = parts[3]
                directed_edges.add((from_city, to_city))
        else:
            cities = conn.split(' and ')
            if len(cities) == 2:
                city1 = cities[0]
                city2 = cities[1]
                directed_edges.add((city1, city2))
                directed_edges.add((city2, city1))
    
    allowed_directed_edges = set()
    for (a_str, b_str) in directed_edges:
        a_index = city_map[a_str]
        b_index = city_map[b_str]
        allowed_directed_edges.add((a_index, b_index))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(9)]
    start_city = [Int(f'start_{i}') for i in range(9)]
    
    for i in range(9):
        s.add(order[i] >= 0, order[i] <= 8)
    s.add(Distinct(order))
    
    def city_duration(city_var):
        return Sum([If(city_var == i, durations[i], 0) for i in range(9)])
    
    s.add(start_city[order[0]] == 1)
    
    for k in range(8):
        s.add(start_city[order[k+1]] == start_city[order[k]] + city_duration(order[k]) - 1)
    
    s.add(start_city[order[8]] + city_duration(order[8]) - 1 == 26)
    
    s.add(start_city[1] >= 8, start_city[1] <= 12)
    s.add(start_city[2] >= 4, start_city[2] <= 10)
    s.add(start_city[5] >= 12, start_city[5] <= 20)
    
    for i in range(9):
        s.add(start_city[i] >= 1)
        s.add(start_city[i] <= 26)
    
    for k in range(8):
        edge_ok = Or([And(order[k] == a, order[k+1] == b) for (a, b) in allowed_directed_edges])
        s.add(edge_ok)
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(9)]
        start_vals = [m.evaluate(start_city[i]).as_long() for i in range(9)]
        
        print("Trip plan:")
        for i in range(9):
            city_idx = order_vals[i]
            city_name = reverse_city_map[city_idx]
            start_day = start_vals[city_idx]
            end_day = start_day + durations[city_idx] - 1
            print(f"From day {start_day} to day {end_day}: stay in {city_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()