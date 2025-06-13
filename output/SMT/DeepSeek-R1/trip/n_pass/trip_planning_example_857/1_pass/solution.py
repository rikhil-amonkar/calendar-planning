from z3 import *

def main():
    # Define city names and their indices
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    n = len(cities)
    idx = {name: i for i, name in enumerate(cities)}
    
    # Required days for each city
    required_days = [0] * n
    required_days[idx['Porto']] = 2
    required_days[idx['Geneva']] = 3
    required_days[idx['Mykonos']] = 3
    required_days[idx['Manchester']] = 4
    required_days[idx['Hamburg']] = 5
    required_days[idx['Naples']] = 5
    required_days[idx['Frankfurt']] = 2
    
    # Direct flight connections (undirected edges)
    edges_list = [
        (idx['Hamburg'], idx['Frankfurt']),
        (idx['Naples'], idx['Mykonos']),
        (idx['Hamburg'], idx['Porto']),
        (idx['Hamburg'], idx['Geneva']),
        (idx['Mykonos'], idx['Geneva']),
        (idx['Frankfurt'], idx['Geneva']),
        (idx['Frankfurt'], idx['Porto']),
        (idx['Geneva'], idx['Porto']),
        (idx['Geneva'], idx['Manchester']),
        (idx['Naples'], idx['Manchester']),
        (idx['Frankfurt'], idx['Naples']),
        (idx['Frankfurt'], idx['Manchester']),
        (idx['Naples'], idx['Geneva']),
        (idx['Porto'], idx['Manchester']),
        (idx['Hamburg'], idx['Manchester'])
    ]
    
    # Create an adjacency matrix
    adj = [[False] * n for _ in range(n)]
    for i, j in edges_list:
        adj[i][j] = True
        adj[j][i] = True
    
    # Create Z3 variables
    s = Solver()
    
    # Order of cities: a permutation of 0 to 6
    order = [Int(f'order_{i}') for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    # Arrival and departure days for each city
    arrive = [Int(f'arrive_{i}') for i in range(n)]
    leave = [Int(f'leave_{i}') for i in range(n)]
    
    # Constraints for the first and last cities
    s.add(arrive[order[0]] == 1)
    s.add(leave[order[n-1]] == 18)
    
    # Constraints for consecutive cities in the order
    for k in range(n-1):
        current_city = order[k]
        next_city = order[k+1]
        # Ensure there is a direct flight between current and next city
        allowed_pairs = []
        for (i, j) in edges_list:
            allowed_pairs.append((i, j))
            allowed_pairs.append((j, i))
        s.add(Or([And(current_city == i, next_city == j) for (i, j) in allowed_pairs]))
        # Departure of current city equals arrival of next city
        s.add(leave[current_city] == arrive[next_city])
    
    # Stay duration constraints
    for i in range(n):
        s.add(leave[i] - arrive[i] + 1 == required_days[i])
        s.add(arrive[i] >= 1, leave[i] <= 18)
        s.add(arrive[i] <= leave[i])
    
    # Event constraints
    mykonos_idx = idx['Mykonos']
    manchester_idx = idx['Manchester']
    frankfurt_idx = idx['Frankfurt']
    
    # Mykonos: at least one day between day 10 and 12
    s.add(arrive[mykonos_idx] <= 12)
    s.add(leave[mykonos_idx] >= 10)
    
    # Manchester: at least one day between day 15 and 18
    s.add(leave[manchester_idx] >= 15)
    
    # Frankfurt: must be present on day 5 and 6
    s.add(arrive[frankfurt_idx] <= 5)
    s.add(leave[frankfurt_idx] >= 6)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        arrive_val = [m.evaluate(arrive[i]).as_long() for i in range(n)]
        leave_val = [m.evaluate(leave[i]).as_long() for i in range(n)]
        
        # Print the itinerary
        print("Found a valid trip plan:")
        for i in range(n-1):
            city_index = order_val[i]
            next_city_index = order_val[i+1]
            start_day = arrive_val[city_index]
            end_day = leave_val[city_index]
            print(f"From day {start_day} to day {end_day}: stay in {cities[city_index]}")
            print(f"On day {end_day}, fly from {cities[city_index]} to {cities[next_city_index]}")
        last_city_index = order_val[n-1]
        start_day_last = arrive_val[last_city_index]
        print(f"From day {start_day_last} to day 18: stay in {cities[last_city_index]}")
    else:
        print("No valid trip plan found.")

if __name__ == "__main__":
    main()