from z3 import *

def main():
    s = Solver()
    
    # Cities: 0: Hamburg, 1: Munich, 2: Manchester, 3: Lyon, 4: Split
    n_days = 20
    city_names = {0: 'Hamburg', 1: 'Munich', 2: 'Manchester', 3: 'Lyon', 4: 'Split'}
    
    # Define valid flight routes (directed edges)
    directed_edges_list = [
        (0, 1), (1, 0),  # Hamburg <-> Munich
        (0, 2), (2, 0),  # Hamburg <-> Manchester
        (0, 4), (4, 0),  # Hamburg <-> Split
        (1, 2), (2, 1),  # Munich <-> Manchester
        (1, 3), (3, 1),  # Munich <-> Lyon
        (1, 4), (4, 1),  # Munich <-> Split
        (3, 4), (4, 3),  # Lyon <-> Split
        (2, 4)            # Manchester -> Split (directed)
    ]
    
    # Decision variables
    start_city = [Int(f'start_city_{i}') for i in range(n_days)]  # City at start of day
    flight_taken = [Bool(f'flight_taken_{i}') for i in range(n_days)]  # Whether flight occurs
    dest_city = [Int(f'dest_city_{i}') for i in range(n_days)]  # Destination if flight taken
    night_city = [Int(f'night_city_{i}') for i in range(n_days)]  # City where night is spent
    
    # Start in Hamburg on Day 1
    s.add(start_city[0] == 0)
    
    # City and flight constraints for each day
    for i in range(n_days):
        # City indices are valid
        s.add(start_city[i] >= 0, start_city[i] <= 4)
        s.add(dest_city[i] >= 0, dest_city[i] <= 4)
        s.add(night_city[i] >= 0, night_city[i] <= 4)
        
        # Night city is destination if flight taken, otherwise start city
        s.add(night_city[i] == If(flight_taken[i], dest_city[i], start_city[i]))
        
        # Flight must be on valid route if taken
        valid_flight = Or([And(start_city[i] == u, dest_city[i] == v) 
                          for (u, v) in directed_edges_list])
        s.add(Implies(flight_taken[i], valid_flight))
        
        # Next day's start city is previous night's city
        if i < n_days - 1:
            s.add(start_city[i+1] == night_city[i])
    
    # Fixed date constraints
    s.add(night_city[12] == 3)  # In Lyon on night of Day 13
    s.add(night_city[13] == 3)  # In Lyon on night of Day 14
    s.add(night_city[18] == 2)  # In Manchester on night of Day 19
    s.add(night_city[19] == 2)  # In Manchester on night of Day 20
    
    # Total days (nights) in each city
    totals = [0] * 5
    for c in range(5):
        # Count how many nights spent in this city
        total_count = Sum([If(night_city[i] == c, 1, 0) for i in range(n_days)])
        totals[c] = total_count
    
    s.add(totals[0] == 7)  # Hamburg
    s.add(totals[1] == 6)  # Munich
    s.add(totals[2] == 2)  # Manchester
    s.add(totals[3] == 2)  # Lyon
    s.add(totals[4] == 7)  # Split
    
    # Generate itinerary if solution exists
    if s.check() == sat:
        m = s.model()
        plan = []
        for i in range(n_days):
            start_val = m.evaluate(start_city[i])
            start_city_name = city_names[start_val.as_long()]
            is_flight = m.evaluate(flight_taken[i])
            
            if is_flight:
                dest_val = m.evaluate(dest_city[i])
                dest_city_name = city_names[dest_val.as_long()]
                plan.append(f"Day {i+1}: Start in {start_city_name}, fly to {dest_city_name}")
            else:
                plan.append(f"Day {i+1}: Stay in {start_city_name}")
        print("\n".join(plan))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()