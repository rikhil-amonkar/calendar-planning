from z3 import *
import json

def main():
    # Define city indices
    M, P, B, S = 0, 1, 2, 3
    city_names = {M: "Madrid", P: "Paris", B: "Bucharest", S: "Seville"}
    
    # Direct flight matrix: [from][to] 
    direct = [
        [0, 1, 1, 1],   # Madrid
        [1, 0, 1, 1],   # Paris
        [1, 1, 0, 0],   # Bucharest
        [1, 1, 0, 0]    # Seville
    ]
    
    # Allowed flight pairs (without self-loop and direct flight exists)
    allowed_pairs = []
    for i in range(4):
        for j in range(4):
            if i != j and direct[i][j] == 1:
                allowed_pairs.append((i, j))
    
    # Segment variables: 4 segments
    n_seg = 4
    s = [Int(f's_{i}') for i in range(n_seg)]
    e = [Int(f'e_{i}') for i in range(n_seg)]
    cities = [Int(f'c_{i}') for i in range(n_seg)]
    
    solver = Solver()
    
    # Segment constraints
    solver.add(s[0] == 1)      # Start on day 1
    solver.add(e[3] == 15)     # End on day 15
    for i in range(n_seg - 1):
        solver.add(e[i] == s[i+1])  # Consecutive segments
    for i in range(n_seg):
        solver.add(s[i] <= e[i])    # Non-empty segments
    
    # City assignments
    for i in range(n_seg):
        solver.add(cities[i] >= 0, cities[i] <= 3)
    
    # Total days per city
    total_days = [7, 6, 2, 3]  # M, P, B, S
    for c in range(4):
        total = 0
        for i in range(n_seg):
            total += If(cities[i] == c, e[i] - s[i] + 1, 0)
        solver.add(total == total_days[c])
    
    # Madrid on days 1-7
    for d in range(1, 8):
        in_city = Or([And(s[i] <= d, d <= e[i], cities[i] == M) for i in range(n_seg)])
        solver.add(in_city)
    
    # Bucharest on days 14-15
    for d in [14, 15]:
        in_city = Or([And(s[i] <= d, d <= e[i], cities[i] == B) for i in range(n_seg)])
        solver.add(in_city)
    
    # Direct flight connections between consecutive segments
    for i in range(n_seg - 1):
        ci = cities[i]
        cj = cities[i+1]
        solver.add(Or([And(ci == a, cj == b) for (a, b) in allowed_pairs]))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.eval(s[i]).as_long() for i in range(n_seg)]
        e_val = [model.eval(e[i]).as_long() for i in range(n_seg)]
        cities_val = [model.eval(cities[i]).as_long() for i in range(n_seg)]
        
        # Build itinerary
        itinerary = []
        for day in range(1, 16):
            for seg in range(n_seg):
                if s_val[seg] <= day <= e_val[seg]:
                    city_name = city_names[cities_val[seg]]
                    itinerary.append({"day": day, "city": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()