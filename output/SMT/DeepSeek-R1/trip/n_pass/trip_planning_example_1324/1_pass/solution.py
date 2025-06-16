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
        ("Copenhagen", "Athens"),
        ("Copenhagen", "Dubrovnik"),
        ("Munich", "Tallinn"),
        ("Copenhagen", "Munich"),
        ("Venice", "Munich"),
        ("Reykjavik", "Athens"),
        ("Athens", "Dubrovnik"),
        ("Venice", "Athens"),
        ("Lyon", "Barcelona"),
        ("Copenhagen", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Athens", "Munich"),
        ("Lyon", "Munich"),
        ("Barcelona", "Reykjavik"),
        ("Venice", "Copenhagen"),
        ("Barcelona", "Dubrovnik"),
        ("Lyon", "Venice"),
        ("Dubrovnik", "Munich"),
        ("Barcelona", "Athens"),
        ("Copenhagen", "Barcelona"),
        ("Venice", "Barcelona"),
        ("Barcelona", "Munich"),
        ("Barcelona", "Tallinn"),
        ("Copenhagen", "Tallinn")
    ]
    
    allowed_edges = set()
    for a_str, b_str in connections:
        a = city_map[a_str]
        b = city_map[b_str]
        allowed_edges.add((a, b))
        allowed_edges.add((b, a))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(9)]
    start_days = [Int(f'start_{i}') for i in range(9)]
    
    for i in range(9):
        s.add(order[i] >= 0, order[i] <= 8)
    
    s.add(Distinct(order))
    
    s.add(start_days[0] == 1)
    
    for i in range(1, 9):
        prev_duration = Sum([If(order[i-1] == j, durations[j], 0) for j in range(9)])
        s.add(start_days[i] == start_days[i-1] + prev_duration - 1)
    
    last_duration = Sum([If(order[8] == j, durations[j], 0) for j in range(9)])
    s.add(start_days[8] + last_duration - 1 == 26)
    
    barcelona_start = Sum([If(order[i] == 1, start_days[i], 0) for i in range(9)])
    s.add(barcelona_start >= 8, barcelona_start <= 12)
    
    copenhagen_start = Sum([If(order[i] == 2, start_days[i], 0) for i in range(9)])
    s.add(copenhagen_start >= 4, copenhagen_start <= 10)
    
    dubrovnik_start = Sum([If(order[i] == 5, start_days[i], 0) for i in range(9)])
    s.add(dubrovnik_start >= 12, dubrovnik_start <= 20)
    
    for i in range(8):
        edge_ok = Or([And(order[i] == a, order[i+1] == b) for (a, b) in allowed_edges])
        s.add(edge_ok)
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(9)]
        start_vals = [m.evaluate(start_days[i]).as_long() for i in range(9)]
        
        print("Trip plan:")
        for i in range(9):
            city_idx = order_vals[i]
            city_name = reverse_city_map[city_idx]
            start_day = start_vals[i]
            duration_city = durations[city_idx]
            end_day = start_day + duration_city - 1
            print(f"From day {start_day} to day {end_day}: stay in {city_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()