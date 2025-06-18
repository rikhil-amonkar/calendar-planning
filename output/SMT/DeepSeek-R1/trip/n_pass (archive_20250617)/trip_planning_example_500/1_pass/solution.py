from z3 import *

def main():
    s = Solver()
    
    # Cities: 0: Hamburg, 1: Munich, 2: Manchester, 3: Lyon, 4: Split
    n_days = 20
    city_names = {0: 'Hamburg', 1: 'Munich', 2: 'Manchester', 3: 'Lyon', 4: 'Split'}
    
    directed_edges_list = [
        (0, 1), (1, 0),
        (0, 2), (2, 0),
        (0, 4), (4, 0),
        (1, 2), (2, 1),
        (1, 3), (3, 1),
        (1, 4), (4, 1),
        (3, 4), (4, 3),
        (2, 4)
    ]
    
    city_day = [Int(f'city_day_{i}') for i in range(1, n_days+1)]
    flight_taken = [Bool(f'flight_taken_{i}') for i in range(1, n_days+1)]
    to_city = [Int(f'to_city_{i}') for i in range(1, n_days+1)]
    
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
    
    # Fixed constraints for day 14 and day 20
    s.add(city_day[13] == 3)  # Day 14 is index 13 (0-based: days 1 to 20 are indices 0 to 19)
    s.add(city_day[19] == 2)  # Day 20 is index 19
    
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
            start_city = m.evaluate(city_day[i])
            is_flight = m.evaluate(flight_taken[i])
            dest_city = m.evaluate(to_city[i])
            start_name = city_names[start_city.as_long()]
            if is_flight:
                dest_name = city_names[dest_city.as_long()]
                plan.append(f"Day {i+1}: Start in {start_name}, fly to {dest_name}")
            else:
                plan.append(f"Day {i+1}: Stay in {start_name}")
        print("\n".join(plan))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()