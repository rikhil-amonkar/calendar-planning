from z3 import *

def main():
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    n = len(cities)
    idx = {city: i for i, city in enumerate(cities)}
    
    required_days = [0] * n
    required_days[idx['Porto']] = 2
    required_days[idx['Geneva']] = 3
    required_days[idx['Mykonos']] = 3
    required_days[idx['Manchester']] = 4
    required_days[idx['Hamburg']] = 5
    required_days[idx['Naples']] = 5
    required_days[idx['Frankfurt']] = 2
    
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
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    arrive_arr = Array('arrive_arr', IntSort(), IntSort())
    leave_arr = Array('leave_arr', IntSort(), IntSort())
    
    for i in range(n):
        s.add(leave_arr[i] - arrive_arr[i] + 1 == required_days[i])
        s.add(arrive_arr[i] >= 1, leave_arr[i] <= 18)
        s.add(arrive_arr[i] <= leave_arr[i])
    
    s.add(arrive_arr[order[0]] == 1)
    s.add(leave_arr[order[n-1]] == 18)
    
    for k in range(n-1):
        city1 = order[k]
        city2 = order[k+1]
        allowed = []
        for (i, j) in edges_list:
            allowed.append(And(city1 == i, city2 == j))
            allowed.append(And(city1 == j, city2 == i))
        s.add(Or(allowed))
        s.add(leave_arr[city1] == arrive_arr[city2])
    
    mykonos_idx = idx['Mykonos']
    manchester_idx = idx['Manchester']
    frankfurt_idx = idx['Frankfurt']
    
    s.add(arrive_arr[mykonos_idx] <= 12, leave_arr[mykonos_idx] >= 10)
    s.add(leave_arr[manchester_idx] >= 15)
    s.add(arrive_arr[frankfurt_idx] <= 5, leave_arr[frankfurt_idx] >= 6)
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(n)]
        arrive_vals = {}
        leave_vals = {}
        for i in range(n):
            arrive_vals[i] = m.evaluate(arrive_arr[i]).as_long()
            leave_vals[i] = m.evaluate(leave_arr[i]).as_long()
        
        print("Found a valid trip plan:")
        for pos in range(n):
            city_idx = order_val[pos]
            city_name = cities[city_idx]
            start = arrive_vals[city_idx]
            end = leave_vals[city_idx]
            print(f"From day {start} to day {end}: stay in {city_name}")
            if pos < n-1:
                next_city_idx = order_val[pos+1]
                next_city_name = cities[next_city_idx]
                print(f"On day {end}, fly from {city_name} to {next_city_name}")
    else:
        print("No valid trip plan found.")

if __name__ == "__main__":
    main()