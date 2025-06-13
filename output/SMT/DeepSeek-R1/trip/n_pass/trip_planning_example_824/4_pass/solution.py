from z3 import *

def main():
    s = Solver()
    s.set("timeout", 300000)  # 5 minutes timeout

    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    city_to_int = {name: idx for idx, name in enumerate(cities)}
    n_days = 22
    n_cities = len(cities)
    
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
    
    Start = [Int('Start_%d' % i) for i in range(n_days)]
    Travel = [Bool('Travel_%d' % i) for i in range(n_days-1)]
    
    for i in range(n_days):
        s.add(Start[i] >= 0, Start[i] < n_cities)
    
    berlin_idx = city_to_int["Berlin"]
    lyon_idx = city_to_int["Lyon"]
    
    for i in range(5):
        s.add(Start[i] == berlin_idx)
    for i in range(5, n_days):
        s.add(Start[i] != berlin_idx)
    
    for i in range(6, 11):
        s.add(Start[i] == lyon_idx)
    for i in list(range(0, 6)) + list(range(11, n_days)):
        s.add(Start[i] != lyon_idx)
    
    for i in range(n_days-1):
        edge_conds = []
        for (u, v) in valid_edges:
            edge_conds.append(And(Start[i] == u, Start[i+1] == v))
        s.add(If(Travel[i], Or(edge_conds), Start[i+1] == Start[i]))
    
    bucharest_idx = city_to_int["Bucharest"]
    s.add(Or(Start[12] == bucharest_idx, Start[13] == bucharest_idx, Start[14] == bucharest_idx))
    
    if s.check() == sat:
        m = s.model()
        print("Day\tStart City\tTravel To")
        for day in range(1, n_days+1):
            start_idx = day - 1
            start_val = m.eval(Start[start_idx]).as_long()
            start_city = cities[start_val]
            if day < n_days:
                travel_val = m.eval(Travel[start_idx])
                if is_true(travel_val):
                    next_val = m.eval(Start[start_idx+1]).as_long()
                    next_city = cities[next_val]
                    print(f"{day}\t{start_city}\t\tTravel to {next_city}")
                else:
                    print(f"{day}\t{start_city}\t\tStay")
            else:
                print(f"{day}\t{start_city}\t\tStay")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()