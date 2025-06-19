from z3 import *

def main():
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    edges = [(0, 4), (4, 1), (1, 3), (0, 5), (2, 0), (5, 4)]
    allowed_edges = []
    for u, v in edges:
        allowed_edges.append((u, v))
        allowed_edges.append((v, u))
    
    s = Solver()
    # Start and end for each day (0-indexed days 0 to 17)
    start = [Int(f'start_{i}') for i in range(18)]
    end = [Int(f'end_{i}') for i in range(18)]
    
    # Each start and end must be a valid city (0-5)
    for i in range(18):
        s.add(And(start[i] >= 0, start[i] < 6))
        s.add(And(end[i] >= 0, end[i] < 6))
    
    # Start of next day must be end of previous day
    for i in range(1, 18):
        s.add(start[i] == end[i-1])
    
    # Flight constraints: if start != end, must be allowed flight
    for i in range(18):
        same_city = start[i] == end[i]
        valid_flight = Or([And(start[i] == u, end[i] == v) for (u, v) in allowed_edges])
        s.add(Or(same_city, valid_flight))
    
    # Count days per city (including travel days)
    def days_in_city(city_idx):
        return Sum([If(Or(start[i] == city_idx, end[i] == city_idx), 1, 0) for i in range(18)])
    
    s.add(days_in_city(0) == 4)  # Helsinki
    s.add(days_in_city(1) == 5)  # Valencia
    s.add(days_in_city(2) == 4)  # Dubrovnik
    s.add(days_in_city(3) == 3)  # Porto
    s.add(days_in_city(4) == 3)  # Prague
    s.add(days_in_city(5) == 4)  # Reykjavik
    
    # Must be in Porto on at least one of days 16,17,18
    porto_days = Or(
        Or(start[15] == 3, end[15] == 3),  # Day 16
        Or(start[16] == 3, end[16] == 3),  # Day 17
        Or(start[17] == 3, end[17] == 3)   # Day 18
    )
    s.add(porto_days)
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        results = []
        for i in range(18):
            s_val = model.evaluate(start[i]).as_long()
            e_val = model.evaluate(end[i]).as_long()
            if s_val == e_val:
                results.append(f"Day {i+1}: Stay in {cities[e_val]}")
            else:
                results.append(f"Day {i+1}: Travel from {cities[s_val]} to {cities[e_val]}, so in both {cities[s_val]} and {cities[e_val]}")
        for res in results:
            print(res)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()