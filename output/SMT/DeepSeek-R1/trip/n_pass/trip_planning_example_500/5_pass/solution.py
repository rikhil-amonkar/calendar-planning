from z3 import *

def main():
    s = Solver()
    
    # Cities: 0: Hamburg, 1: Munich, 2: Manchester, 3: Lyon, 4: Split
    n_days = 20
    city_names = {0: 'Hamburg', 1: 'Munich', 2: 'Manchester', 3: 'Lyon', 4: 'Split'}
    
    # Valid flight routes (directed edges)
    directed_edges = [
        (0, 1), (1, 0),  # Hamburg <-> Munich
        (0, 2), (2, 0),  # Hamburg <-> Manchester
        (0, 4), (4, 0),  # Hamburg <-> Split
        (1, 2), (2, 1),  # Munich <-> Manchester
        (1, 3), (3, 1),  # Munich <-> Lyon
        (1, 4), (4, 1),  # Munich <-> Split
        (3, 4), (4, 3),  # Lyon <-> Split
        (2, 4)            # Manchester -> Split
    ]
    
    # Decision variables
    start_city = [Int(f'start_city_{i}') for i in range(n_days)]
    flight_taken = [Bool(f'flight_taken_{i}') for i in range(n_days)]
    dest_city = [Int(f'dest_city_{i}') for i in range(n_days)]
    
    # Start in Hamburg on day 1
    s.add(start_city[0] == 0)
    
    # Continuity constraint between days
    for i in range(n_days - 1):
        s.add(start_city[i+1] == If(flight_taken[i], dest_city[i], start_city[i]))
    
    # Flight validity constraints
    for i in range(n_days):
        s.add(start_city[i] >= 0, start_city[i] <= 4)
        s.add(dest_city[i] >= 0, dest_city[i] <= 4)
        
        # Valid flight must be in directed_edges
        valid_flight = Or([And(start_city[i] == u, dest_city[i] == v) for (u, v) in directed_edges])
        s.add(Implies(flight_taken[i], valid_flight))
        
        # Cannot fly from and to the same city
        s.add(Implies(flight_taken[i], start_city[i] != dest_city[i]))
    
    # Fixed date constraints (must be present in city on these days)
    s.add(Or(start_city[12] == 3, And(flight_taken[12], dest_city[12] == 3)))  # Lyon on day 13
    s.add(Or(start_city[13] == 3, And(flight_taken[13], dest_city[13] == 3)))  # Lyon on day 14
    s.add(Or(start_city[18] == 2, And(flight_taken[18], dest_city[18] == 2)))  # Manchester on day 19
    s.add(Or(start_city[19] == 2, And(flight_taken[19], dest_city[19] == 2)))  # Manchester on day 20
    
    # Count days per city (count start and arrivals)
    counts = [0]*5
    for c in range(5):
        total = 0
        for i in range(n_days):
            # Count if started in city c
            total += If(start_city[i] == c, 1, 0)
            # Count if flight arrived in city c
            total += If(And(flight_taken[i], dest_city[i] == c), 1, 0)
        counts[c] = total
    
    # Apply required day counts
    s.add(counts[0] == 7)  # Hamburg
    s.add(counts[1] == 6)  # Munich
    s.add(counts[2] == 2)  # Manchester
    s.add(counts[3] == 2)  # Lyon
    s.add(counts[4] == 7)  # Split
    
    # Generate itinerary if solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            start_val = m.evaluate(start_city[i])
            start_city_idx = start_val.as_long()
            start_name = city_names[start_city_idx]
            
            if m.evaluate(flight_taken[i]):
                dest_val = m.evaluate(dest_city[i])
                dest_city_idx = dest_val.as_long()
                dest_name = city_names[dest_city_idx]
                itinerary.append(f"Day {i+1}: Start in {start_name}, fly to {dest_name}")
            else:
                itinerary.append(f"Day {i+1}: Stay in {start_name}")
        print("\n".join(itinerary))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()