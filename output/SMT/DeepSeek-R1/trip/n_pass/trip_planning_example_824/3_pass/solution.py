from z3 import *

def main():
    s = Solver()
    s.set("timeout", 300000)  # 5 minutes timeout

    # Define cities
    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    city_to_int = {name: idx for idx, name in enumerate(cities)}
    n_days = 22
    n_cities = len(cities)
    
    # Define valid edges (direct flights)
    bidirectional = [
        ("Lisbon", "Bucharest"), 
        ("Berlin", "Lisbon"), 
        ("Bucharest", "Riga"), 
        ("Berlin", "Riga"), 
        ("Split", "Lyon"), 
        ("Lisbon", "Riga"), 
        ("Berlin", "Split"), 
        ("Lyon", "Lisbon"), 
        ("Berlin", "Tallinn"), 
        ("Lyon", "Bucharest")
    ]
    unidirectional = [("Riga", "Tallinn")]
    
    valid_edges_set = set()
    for u, v in bidirectional:
        valid_edges_set.add((city_to_int[u], city_to_int[v]))
        valid_edges_set.add((city_to_int[v], city_to_int[u]))
    for u, v in unidirectional:
        valid_edges_set.add((city_to_int[u], city_to_int[v]))
    valid_edges = list(valid_edges_set)
    
    # Define variables
    Start = [Int('Start_%d' % i) for i in range(23)]  # 23 starts for 22 days
    Travel = [Bool('Travel_%d' % i) for i in range(22)]  # 22 travel days
    
    # Start constraints: each between 0-6
    for i in range(23):
        s.add(Start[i] >= 0, Start[i] < n_cities)
    
    # Berlin: days 1-5 (start city)
    for i in range(5):
        s.add(Start[i] == city_to_int["Berlin"])
    # After day 5, no Berlin
    for i in range(5, 23):
        s.add(Start[i] != city_to_int["Berlin"])
    
    # Lyon: days 7-11 (start city)
    lyon_idx = city_to_int["Lyon"]
    for i in range(6, 11):  # Start indices 6 to 10 (days 7-11)
        s.add(Start[i] == lyon_idx)
    # Lyon not allowed outside these days
    for i in list(range(0, 6)) + list(range(11, 23)):
        s.add(Start[i] != lyon_idx)
    
    # Travel constraints
    for idx in range(22):
        edge_conds = []
        for (u, v) in valid_edges:
            edge_conds.append(And(Start[idx] == u, Start[idx+1] == v))
        s.add(If(Travel[idx], Or(edge_conds), Start[idx+1] == Start[idx]))
    
    # City days constraints
    required_days = {
        "Split": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4
    }
    # Add fixed cities for completeness
    required_days["Berlin"] = 5
    required_days["Lyon"] = 5
    
    for city, days in required_days.items():
        c = city_to_int[city]
        total = 0
        for i in range(22):  # Days 1-22 use Start[0] to Start[21]
            total += If(Start[i] == c, 1, 0)
        s.add(total == days)
    
    # Bucharest must have at least one day in [13,15]
    bucharest_idx = city_to_int["Bucharest"]
    s.add(Or(
        Start[12] == bucharest_idx,  # Day 13
        Start[13] == bucharest_idx,  # Day 14
        Start[14] == bucharest_idx   # Day 15
    ))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        print("Day\tStart City\tTravel To")
        for day in range(1, 23):
            start_idx = day - 1
            start_val = m.eval(Start[start_idx]).as_long()
            start_city = cities[start_val]
            travel_val = m.eval(Travel[start_idx])
            
            if is_true(travel_val):
                next_val = m.eval(Start[start_idx+1]).as_long()
                next_city = cities[next_val]
                print(f"{day}\t{start_city}\t\tTravel to {next_city}")
            else:
                print(f"{day}\t{start_city}\t\tStay")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()