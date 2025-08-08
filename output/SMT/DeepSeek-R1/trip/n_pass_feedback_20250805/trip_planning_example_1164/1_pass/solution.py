from z3 import *
import json

def main():
    # City names and their indices
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    # Required stays for each city
    stays = [2, 2, 5, 3, 4, 3, 3, 2]
    
    # Build the direct flight edge set
    edges_str = [
        "Copenhagen and Vienna",
        "Nice and Stockholm",
        "Split and Copenhagen",
        "Nice and Reykjavik",
        "Nice and Porto",
        "Reykjavik and Vienna",
        "Stockholm and Copenhagen",
        "Nice and Venice",
        "Nice and Vienna",
        "Reykjavik and Copenhagen",
        "Nice and Copenhagen",
        "Stockholm and Vienna",
        "Venice and Vienna",
        "Copenhagen and Porto",
        "Reykjavik and Stockholm",
        "Stockholm and Split",
        "Split and Vienna",
        "Copenhagen and Venice",
        "Vienna and Porto"
    ]
    
    edge_set = set()
    for e in edges_str:
        parts = e.split(' and ')
        a_name = parts[0].strip()
        b_name = parts[1].strip()
        idx1 = cities.index(a_name)
        idx2 = cities.index(b_name)
        key = (min(idx1, idx2), max(idx1, idx2))
        edge_set.add(key)
    
    # Create Z3 variables
    c0, c1, c2, c3, c4, c5, c6, c7 = Ints('c0 c1 c2 c3 c4 c5 c6 c7')
    c = [c0, c1, c2, c3, c4, c5, c6, c7]
    f0, f1, f2, f3, f4, f5, f6 = Ints('f0 f1 f2 f3 f4 f5 f6')
    f = [f0, f1, f2, f3, f4, f5, f6]  # f0 is f1, f1 is f2, ... f6 is f7 in the problem
    
    s = Solver()
    
    # Constraints: permutation
    s.add([And(ci >= 0, ci <= 7) for ci in c])
    s.add(Distinct(c))
    
    # Flight day constraints
    s.add(f0 == stays[c0])
    s.add(f1 == f0 + stays[c1] - 1)
    s.add(f2 == f1 + stays[c2] - 1)
    s.add(f3 == f2 + stays[c3] - 1)
    s.add(f4 == f3 + stays[c4] - 1)
    s.add(f5 == f4 + stays[c5] - 1)
    s.add(f6 == f5 + stays[c6] - 1)
    s.add(f6 == 18 - stays[c7])
    
    # Flight days are increasing and within bounds
    s.add(f0 >= 1)
    s.add(f0 < f1, f1 < f2, f2 < f3, f3 < f4, f4 < f5, f5 < f6)
    s.add(f6 <= 17)
    
    # Direct flight constraints
    for i in range(7):
        a = c[i]
        b = c[i+1]
        min_ab = If(a <= b, a, b)
        max_ab = If(a <= b, b, a)
        edge_constraints = []
        for edge in edge_set:
            edge_constraints.append(And(min_ab == edge[0], max_ab == edge[1]))
        s.add(Or(edge_constraints))
    
    # Event constraints
    reykjavik_index = 0
    stockholm_index = 1
    vienna_index = 5
    porto_index = 2
    
    reyk_cond = []
    stock_cond = []
    vienna_cond = []
    porto_cond = []
    
    for j in range(8):
        if j == 0:
            start_j = 1
            end_j = f0
        elif j == 7:
            start_j = f6
            end_j = 17
        else:
            start_j = f[j-1]
            end_j = f[j]
        
        # Reykjavik: at least one of day3 or day4
        cond_reyk = Or(And(start_j <= 3, 3 <= end_j), And(start_j <= 4, 4 <= end_j))
        reyk_cond.append(And(c[j] == reykjavik_index, cond_reyk))
        
        # Stockholm: at least one of day4 or day5
        cond_stock = Or(And(start_j <= 4, 4 <= end_j), And(start_j <= 5, 5 <= end_j))
        stock_cond.append(And(c[j] == stockholm_index, cond_stock))
        
        # Vienna: must cover [11,13]
        cond_vienna = And(start_j <= 11, end_j >= 13)
        vienna_cond.append(And(c[j] == vienna_index, cond_vienna))
        
        # Porto: must cover [13,17]
        cond_porto = And(start_j <= 13, end_j >= 17)
        porto_cond.append(And(c[j] == porto_index, cond_porto))
    
    s.add(Or(reyk_cond))
    s.add(Or(stock_cond))
    s.add(Or(vienna_cond))
    s.add(Or(porto_cond))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        c_vals = [m.evaluate(c_i).as_long() for c_i in c]
        f_vals = [m.evaluate(f_i).as_long() for f_i in f]
        
        # Map to city names
        city_permutation = [cities[idx] for idx in c_vals]
        flight_days = f_vals  # f0 to f6: flight days after city0 to city6
        
        # Build itinerary for each day
        itinerary = []
        for d in range(1, 18):  # days 1 to 17
            current_cities = []
            # Check city0 (first city)
            if d <= flight_days[0]:
                current_cities.append(city_permutation[0])
            # Check city1
            if d >= flight_days[0] and d <= flight_days[1]:
                current_cities.append(city_permutation[1])
            # Check city2
            if d >= flight_days[1] and d <= flight_days[2]:
                current_cities.append(city_permutation[2])
            # Check city3
            if d >= flight_days[2] and d <= flight_days[3]:
                current_cities.append(city_permutation[3])
            # Check city4
            if d >= flight_days[3] and d <= flight_days[4]:
                current_cities.append(city_permutation[4])
            # Check city5
            if d >= flight_days[4] and d <= flight_days[5]:
                current_cities.append(city_permutation[5])
            # Check city6
            if d >= flight_days[5] and d <= flight_days[6]:
                current_cities.append(city_permutation[6])
            # Check city7 (last city)
            if d >= flight_days[6]:
                current_cities.append(city_permutation[7])
            
            # Format as a comma-separated string if multiple cities, else single
            city_str = ",".join(current_cities)
            itinerary.append({"day": d, "city": city_str})
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()