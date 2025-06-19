from z3 import *

def main():
    # City indices
    cities = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
    n = 8
    # Required days for each city
    days_req = [4, 5, 4, 4, 2, 2, 4, 5]
    # Adjusted days (required_days - 1)
    adj_days = [d - 1 for d in days_req]  # [3,4,3,3,1,1,3,4]
    
    # Graph of direct flights (undirected)
    graph = {
        0: [1, 2, 4, 5],    # Riga
        1: [0, 2, 4, 5, 7], # Manchester
        2: [0, 1, 4, 5],    # Bucharest
        3: [4],              # Florence
        4: [0, 1, 2, 3, 6, 7], # Vienna
        5: [0, 1, 2, 7],     # Istanbul
        6: [4, 7],           # Reykjavik
        7: [1, 4, 5, 6]      # Stuttgart
    }
    
    # Build list of all edges (both directions)
    edges_all = []
    for u in range(n):
        for v in graph[u]:
            edges_all.append((u, v))
    
    # Create Z3 variables for the sequence
    s = [Int(f's{i}') for i in range(n)]
    
    # Constraints for the sequence
    constraints = []
    # Each s[i] must be between 0 and 7
    constraints.extend([And(s[i] >= 0, s[i] < n) for i in range(n)])
    # All cities must be distinct
    constraints.append(Distinct(s))
    
    # Flight connections: for each consecutive pair, (s[i], s[i+1]) must be in edges_all
    for i in range(n - 1):
        constraints.append(Or([And(s[i] == u, s[i + 1] == v) for (u, v) in edges_all]))
    
    # Variables for positions of Istanbul and Bucharest
    k = Int('k')  # position of Istanbul (city index 5)
    m = Int('m')  # position of Bucharest (city index 2)
    
    # Istanbul must be at some position k
    constraints.append(Or([And(s[i] == 5, k == i) for i in range(n)]))
    # Bucharest must be at some position m
    constraints.append(Or([And(s[i] == 2, m == i) for i in range(n)]))
    
    # Cumulative sum for cities before Istanbul: must be 11
    cum_ist = Int('cum_ist')
    cum_ist_expr = Sum([If(j < k, adj_days[s[j]], 0) for j in range(n)])
    constraints.append(cum_ist_expr == 11)
    
    # Start day of Bucharest: 1 + cumulative sum of adjusted days for cities before it
    start_buch = Int('start_buch')
    cum_buch_expr = Sum([If(j < m, adj_days[s[j]], 0) for j in range(n)])
    constraints.append(start_buch == 1 + cum_buch_expr)
    constraints.append(And(start_buch >= 13, start_buch <= 19))
    
    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        seq = [model.eval(s[i]).as_long() for i in range(n)]
        # Map indices to city names
        seq_cities = [cities[idx] for idx in seq]
        print("Found a valid sequence:")
        print(" -> ".join(seq_cities))
        
        # Compute start and end days for each city in the sequence
        start_day = 1
        schedule = []
        for i in range(n):
            city_idx = seq[i]
            city_name = cities[city_idx]
            dur = days_req[city_idx]
            end_day = start_day + dur - 1
            schedule.append((city_name, start_day, end_day))
            # Next city starts on the same day we end (travel day)
            start_day = end_day
        
        print("\nSchedule:")
        for city, start, end in schedule:
            print(f"{city}: from day {start} to {end}")
    else:
        print("No valid trip plan found.")

if __name__ == "__main__":
    main()