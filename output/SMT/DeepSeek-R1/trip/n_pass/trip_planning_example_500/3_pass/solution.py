from z3 import *

def main():
    s = Solver()
    
    # Cities: 0: Hamburg, 1: Munich, 2: Manchester, 3: Lyon, 4: Split
    n_days = 20
    city_names = {0: 'Hamburg', 1: 'Munich', 2: 'Manchester', 3: 'Lyon', 4: 'Split'}
    
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
    
    city_day = [Int(f'city_day_{i}') for i in range(n_days)]
    flight_taken = [Bool(f'flight_taken_{i}') for i in range(n_days)]
    to_city = [Int(f'to_city_{i}') for i in range(n_days)]
    
    # Start in Hamburg on day 1
    s.add(city_day[0] == 0)
    
    # Constraints for each day
    for i in range(n_days):
        s.add(city_day[i] >= 0, city_day[i] <= 4)
        s.add(to_city[i] >= 0, to_city[i] <= 4)
        
        edge_constraints = []
        for (u, v) in directed_edges_list:
            edge_constraints.append(And(city_day[i] == u, to_city[i] == v))
        s.add(Implies(flight_taken[i], Or(edge_constraints)))
    
    # Continuity constraints
    for i in range(n_days - 1):
        s.add(city_day[i+1] == If(flight_taken[i], to_city[i], city_day[i]))
    
    # Fixed constraints
    # Day 13 (index 12): must end in Lyon
    s.add(Or(
        And(city_day[12] == 3, Not(flight_taken[12])),
        And(flight_taken[12], to_city[12] == 3)
    ))
    # Day 14 (index 13): must start in Lyon and stay
    s.add(city_day[13] == 3)
    s.add(Not(flight_taken[13]))
    # Day 19 (index 18): must end in Manchester
    s.add(Or(
        And(city_day[18] == 2, Not(flight_taken[18])),
        And(flight_taken[18], to_city[18] == 2)
    ))
    # Day 20 (index 19): must start in Manchester and stay
    s.add(city_day[19] == 2)
    s.add(Not(flight_taken[19]))
    
    # Total days per city
    totals = [0] * 5
    for c in range(5):
        total_count = 0
        for i in range(n_days):
            total_count += If(city_day[i] == c, 1, 0)
            total_count += If(And(flight_taken[i], to_city[i] == c), 1, 0)
        totals[c] = total_count
    
    s.add(totals[0] == 7)  # Hamburg
    s.add(totals[1] == 6)  # Munich
    s.add(totals[2] == 2)  # Manchester
    s.add(totals[3] == 2)  # Lyon
    s.add(totals[4] == 7)  # Split
    
    # Check and output the solution
    if s.check() == sat:
        m = s.model()
        plan = []
        for i in range(n_days):
            start_city_val = m.evaluate(city_day[i])
            start_city_num = start_city_val.as_long()
            start_city_name = city_names[start_city_num]
            is_flight = m.evaluate(flight_taken[i])
            if is_flight:
                dest_city_val = m.evaluate(to_city[i])
                dest_city_num = dest_city_val.as_long()
                dest_city_name = city_names[dest_city_num]
                plan.append(f"Day {i+1}: Start in {start_city_name}, fly to {dest_city_name}")
            else:
                plan.append(f"Day {i+1}: Stay in {start_city_name}")
        print("\n".join(plan))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()