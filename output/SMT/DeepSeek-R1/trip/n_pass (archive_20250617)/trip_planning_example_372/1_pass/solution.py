from z3 import *

def main():
    n_days = 13
    n_cities = 4
    cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
    edges = [(0, 1), (0, 2), (1, 2), (2, 3)]
    
    start_city = [Int(f'start_city_{i}') for i in range(1, n_days+1)]
    travel = [Bool(f'travel_{i}') for i in range(1, n_days+1)]
    dest_city = [Int(f'dest_city_{i}') for i in range(1, n_days+1)]
    
    s = Solver()
    
    for i in range(n_days):
        s.add(start_city[i] >= 0, start_city[i] < n_cities)
        s.add(dest_city[i] >= 0, dest_city[i] < n_cities)
    
    for i in range(1, n_days):
        end_city_prev = If(travel[i-1], dest_city[i-1], start_city[i-1])
        s.add(start_city[i] == end_city_prev)
    
    in_city = []
    for i in range(n_days):
        in_city_day = []
        for c in range(n_cities):
            in_city_c = If(travel[i], 
                           Or(start_city[i] == c, dest_city[i] == c),
                           start_city[i] == c)
            in_city_day.append(in_city_c)
        in_city.append(in_city_day)
    
    for i in range(4):
        s.add(in_city[i][0] == True)
    for i in range(4, n_days):
        s.add(in_city[i][0] == False)
    
    s.add(in_city[6][3] == True)
    s.add(in_city[12][3] == True)
    
    totals = [0]*n_cities
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            total += If(in_city[i][c], 1, 0)
        totals[c] = total
    
    s.add(totals[0] == 4)
    s.add(totals[1] == 2)
    s.add(totals[2] == 3)
    s.add(totals[3] == 7)
    
    for i in range(n_days):
        allowed_pairs = []
        for (a, b) in edges:
            allowed_pairs.append(And(start_city[i] == a, dest_city[i] == b))
            allowed_pairs.append(And(start_city[i] == b, dest_city[i] == a))
        s.add(Implies(travel[i], Or(allowed_pairs)))
    
    total_travel = Sum([If(travel[i], 1, 0) for i in range(n_days)])
    s.add(total_travel == 3)
    
    if s.check() == sat:
        m = s.model()
        start_city_val = [m.evaluate(start_city[i]).as_long() for i in range(n_days)]
        travel_val = [m.evaluate(travel[i]) for i in range(n_days)]
        dest_city_val = [m.evaluate(dest_city[i]).as_long() for i in range(n_days)]
        
        for i in range(n_days):
            if is_true(travel_val[i]):
                city_list = [cities[start_city_val[i]], cities[dest_city_val[i]]]
                print(f"Day {i+1}: {city_list}")
            else:
                city_list = [cities[start_city_val[i]]]
                print(f"Day {i+1}: {city_list}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()