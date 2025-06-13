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
    
    # Define variables: Start for 23 days (index 0 to 22) and Travel for 22 days (index 0 to 21)
    Start = [Int('Start_%d' % i) for i in range(23)]
    Travel = [Bool('Travel_%d' % i) for i in range(22)]
    
    # Constraints for Start: each must be between 0 and 6
    for i in range(23):
        s.add(Start[i] >= 0, Start[i] < n_cities)
    
    # Fixed stays in Berlin (days 1-5): Start[0] to Start[4] must be Berlin (0)
    for i in range(5):
        s.add(Start[i] == city_to_int["Berlin"])
    # After day 5, no Berlin: Start[5] to Start[21] (days 6 to 22) not Berlin
    for i in range(5, 22):
        s.add(Start[i] != city_to_int["Berlin"])
    
    # Lyon constraints: must be in Lyon on days 7-11
    lyon = city_to_int["Lyon"]
    for d in [7, 8, 9, 10, 11]:
        idx = d - 1
        s.add(Or(Start[idx] == lyon, And(Travel[idx], Start[idx+1] == lyon)))
    # Lyon not allowed on days 1-6 and 12-22
    for d in range(1, 7):  # days 1 to 6
        idx = d - 1
        s.add(Start[idx] != lyon)
        s.add(Implies(Travel[idx], Start[idx+1] != lyon))
    for d in range(12, 23):  # days 12 to 22
        idx = d - 1
        s.add(Start[idx] != lyon)
        if d < 23:  # Avoid index out of bounds for Travel (d=22: idx=21, Travel[21] exists)
            s.add(Implies(Travel[idx], Start[idx+1] != lyon))
    
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
    # Additional cities for which we want to ensure total days (already constrained but for completeness)
    required_days["Berlin"] = 5
    required_days["Lyon"] = 5
    
    for city_name, total_req in required_days.items():
        c = city_to_int[city_name]
        total_days = 0
        for d in range(1, n_days+1):  # days 1 to 22
            idx = d - 1
            in_city = Or(Start[idx] == c, And(Travel[idx], Start[idx+1] == c))
            total_days += If(in_city, 1, 0)
        s.add(total_days == total_req)
    
    # Bucharest must have at least one day in [13,15]
    bucharest = city_to_int["Bucharest"]
    days_constraint = []
    for d in [13, 14, 15]:
        idx = d - 1
        in_city = Or(Start[idx] == bucharest, And(Travel[idx], Start[idx+1] == bucharest))
        days_constraint.append(in_city)
    s.add(Or(days_constraint))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        # Print the schedule
        print("Day\tStart City\tTravel To")
        for d in range(1, n_days+1):
            idx = d - 1
            start_city_val = m.eval(Start[idx]).as_long()
            start_city_name = cities[start_city_val]
            travel_val = m.eval(Travel[idx])
            if is_true(travel_val):
                next_city_val = m.eval(Start[idx+1]).as_long()
                next_city_name = cities[next_city_val]
                print(f"{d}\t{start_city_name}\t\tTravel to {next_city_name}")
            else:
                print(f"{d}\t{start_city_name}\t\tStay")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()