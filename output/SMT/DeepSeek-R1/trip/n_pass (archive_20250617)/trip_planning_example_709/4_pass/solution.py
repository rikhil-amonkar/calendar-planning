from z3 import *

def main():
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    edges = [(0, 4), (4, 1), (1, 3), (0, 5), (2, 0), (5, 4)]
    allowed_edges = []
    for u, v in edges:
        allowed_edges.append((u, v))
        allowed_edges.append((v, u))
    
    s = Solver()
    start = [Int(f'start_{i}') for i in range(18)]
    end = [Int(f'end_{i}') for i in range(18)]
    
    for i in range(18):
        s.add(And(start[i] >= 0, start[i] < 6))
        s.add(And(end[i] >= 0, end[i] < 6))
    
    for i in range(17):
        s.add(end[i] == start[i+1])
    
    for i in range(18):
        same_city = (start[i] == end[i])
        valid_flight = Or([And(start[i] == u, end[i] == v) for (u, v) in allowed_edges])
        s.add(Or(same_city, valid_flight))
    
    counts = [0] * 6
    for c in range(6):
        counts[c] = Sum([If(Or(start[i] == c, end[i] == c), 1, 0) for i in range(18)])
    
    s.add(counts[0] == 4)  # Helsinki
    s.add(counts[1] == 5)  # Valencia
    s.add(counts[2] == 4)  # Dubrovnik
    s.add(counts[3] == 3)  # Porto
    s.add(counts[4] == 3)  # Prague
    s.add(counts[5] == 4)  # Reykjavik
    
    porto_days = Or(
        Or(start[15] == 3, end[15] == 3),
        Or(start[16] == 3, end[16] == 3),
        Or(start[17] == 3, end[17] == 3)
    )
    s.add(porto_days)
    
    if s.check() == sat:
        model = s.model()
        results = []
        for i in range(18):
            s_val = model.evaluate(start[i]).as_long()
            e_val = model.evaluate(end[i]).as_long()
            if s_val == e_val:
                results.append(f"Day {i+1}: Stay in {cities[s_val]}")
            else:
                results.append(f"Day {i+1}: Travel from {cities[s_val]} to {cities[e_val]}, so in both {cities[s_val]} and {cities[e_val]}")
        for res in results:
            print(res)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()