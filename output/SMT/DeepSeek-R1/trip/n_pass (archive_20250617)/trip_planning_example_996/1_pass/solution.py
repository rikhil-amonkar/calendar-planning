from z3 import *

def main():
    # Define city indices
    cities = {
        "Mykonos": 0,
        "Nice": 1,
        "Zurich": 2,
        "Prague": 3,
        "Bucharest": 4,
        "Valencia": 5,
        "Riga": 6
    }
    idx_to_city = {v: k for k, v in cities.items()}
    
    # Required days per city
    required_days = {
        cities["Mykonos"]: 3,
        cities["Nice"]: 2,
        cities["Zurich"]: 5,
        cities["Prague"]: 3,
        cities["Bucharest"]: 5,
        cities["Valencia"]: 5,
        cities["Riga"]: 5
    }
    
    # Direct flights as tuples (min, max) for undirected edges
    allowed_edges = set([
        (0, 1), (0, 2), (1, 2), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6),
        (3, 4), (3, 5), (3, 6), (4, 5), (4, 6)
    ])
    
    # Initialize Z3 variables
    s_start = [Int(f's_start_{i}') for i in range(22)]
    s_end = [Int(f's_end_{i}') for i in range(22)]
    
    solver = Solver()
    
    # Domain constraints: each city index between 0 and 6
    for i in range(22):
        solver.add(s_start[i] >= 0, s_start[i] <= 6)
        solver.add(s_end[i] >= 0, s_end[i] <= 6)
    
    # Continuity constraint: end of day i must equal start of day i+1
    for i in range(21):
        solver.add(s_end[i] == s_start[i + 1])
    
    # Count constraints: for each city, count days where it appears as start or end
    for city_idx, req in required_days.items():
        count = 0
        for i in range(22):
            count += If(Or(s_start[i] == city_idx, s_end[i] == city_idx), 1, 0)
        solver.add(count == req)
    
    # Event constraints
    # Mykonos must be visited on at least one day in [1,3] (indices 0,1,2)
    solver.add(Or([Or(s_start[i] == 0, s_end[i] == 0) for i in [0, 1, 2]]))
    # Prague must be visited on at least one day in [7,9] (indices 6,7,8)
    solver.add(Or([Or(s_start[i] == 3, s_end[i] == 3) for i in [6, 7, 8]]))
    
    # Flight constraints: if start and end differ, must have a direct flight
    for i in range(22):
        conds = [s_start[i] == s_end[i]]
        for a, b in allowed_edges:
            conds.append(And(s_start[i] == a, s_end[i] == b))
            conds.append(And(s_start[i] == b, s_end[i] == a))
        solver.add(Or(conds))
    
    # Travel days must be exactly 6
    travel_days = Sum([If(s_start[i] != s_end[i], 1, 0) for i in range(22)])
    solver.add(travel_days == 6)
    
    # Check and output the solution
    if solver.check() == sat:
        model = solver.model()
        schedule = []
        for i in range(22):
            start_val = model.eval(s_start[i]).as_long()
            end_val = model.eval(s_end[i]).as_long()
            start_city = idx_to_city[start_val]
            if start_val == end_val:
                schedule.append(f"Day {i + 1}: {start_city}")
            else:
                end_city = idx_to_city[end_val]
                schedule.append(f"Day {i + 1}: {start_city} and {end_city}")
        
        # Print the schedule
        for day in schedule:
            print(day)
            
        # Verify counts for debugging
        counts = {city: 0 for city in cities}
        for i in range(22):
            start_val = model.eval(s_start[i]).as_long()
            end_val = model.eval(s_end[i]).as_long()
            city_start = idx_to_city[start_val]
            counts[city_start] += 1
            if start_val != end_val:
                city_end = idx_to_city[end_val]
                counts[city_end] += 1
        print("\nCounts per city:")
        for city, count in counts.items():
            print(f"{city}: {count} days")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()