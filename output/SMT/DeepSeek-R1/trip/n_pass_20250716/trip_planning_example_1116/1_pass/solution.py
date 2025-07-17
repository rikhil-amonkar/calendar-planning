from z3 import *
import json

def main():
    # The 6 cities and their days (excluding Oslo and Frankfurt)
    cities = ['Reykjavik', 'Stockholm', 'Munich', 'Barcelona', 'Bucharest', 'Split']
    days = [5, 4, 4, 3, 2, 3]  # Corresponding days for the cities

    # Build the flight list
    flight_list = [
        "Reykjavik and Munich", 
        "Munich and Frankfurt", 
        "Split and Oslo", 
        "Reykjavik and Oslo", 
        "Bucharest and Munich", 
        "Oslo and Frankfurt", 
        "Bucharest and Barcelona", 
        "Barcelona and Frankfurt", 
        "Reykjavik and Frankfurt", 
        "Barcelona and Stockholm", 
        "Barcelona and Reykjavik", 
        "Stockholm and Reykjavik", 
        "Barcelona and Split", 
        "Bucharest and Oslo", 
        "Bucharest and Frankfurt", 
        "Split and Stockholm", 
        "Barcelona and Oslo", 
        "Stockholm and Munich", 
        "Stockholm and Oslo", 
        "Split and Frankfurt", 
        "Barcelona and Munich", 
        "Stockholm and Frankfurt", 
        "Munich and Oslo", 
        "Split and Munich"
    ]
    
    edges = set()
    for s in flight_list:
        parts = s.split(' and ')
        u = parts[0]
        v = parts[1]
        edges.add((u, v))
        edges.add((v, u))
    
    # Build adjacency matrix for the 6 cities and adjacency list for Oslo
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    adj6 = [[False] * 6 for _ in range(6)]
    adj_oslo = [False] * 6
    
    for (u, v) in edges:
        if u in city_to_index and v in city_to_index:
            i = city_to_index[u]
            j = city_to_index[v]
            adj6[i][j] = True
            adj6[j][i] = True
        elif u == 'Oslo' and v in city_to_index:
            j = city_to_index[v]
            adj_oslo[j] = True
        elif v == 'Oslo' and u in city_to_index:
            j = city_to_index[u]
            adj_oslo[j] = True
    
    s = Solver()
    city_vars = [Int(f'city_{i}') for i in range(6)]
    for i in range(6):
        s.add(city_vars[i] >= 0, city_vars[i] < 6)
    s.add(Distinct(city_vars))
    
    d_arr = [days[city_vars[i]] for i in range(6)]
    
    S = [Int(f'S_{i}') for i in range(6)]
    E = [Int(f'E_{i}') for i in range(6)]
    
    s.add(S[0] == 1)
    s.add(E[0] == S[0] + d_arr[0] - 1)
    for i in range(1, 6):
        s.add(S[i] == E[i-1])
        s.add(E[i] == S[i] + d_arr[i] - 1)
    s.add(E[5] == 16)
    
    for i in range(5):
        options = []
        for a in range(6):
            for b in range(6):
                if adj6[a][b]:
                    options.append(And(city_vars[i] == a, city_vars[i+1] == b))
        s.add(Or(options))
    
    s.add(Or([city_vars[5] == i for i in range(6) if adj_oslo[i]]))
    
    rey_constraints = []
    munich_constraints = []
    for i in range(6):
        rey_constraints.append(If(city_vars[i] == 0, And(S[i] <= 13, E[i] >= 9), True))
        munich_constraints.append(If(city_vars[i] == 2, And(S[i] <= 16, E[i] >= 13), True))
    s.add(And(rey_constraints))
    s.add(And(munich_constraints))
    
    if s.check() == sat:
        m = s.model()
        assignment = [m.evaluate(city_vars[i]).as_long() for i in range(6)]
        path_cities = [cities[assignment[i]] for i in range(6)]
        path_days = [days[assignment[i]] for i in range(6)]
        
        s0 = 1
        e0 = s0 + path_days[0] - 1
        s1 = e0
        e1 = s1 + path_days[1] - 1
        s2 = e1
        e2 = s2 + path_days[2] - 1
        s3 = e2
        e3 = s3 + path_days[3] - 1
        s4 = e3
        e4 = s4 + path_days[4] - 1
        s5 = e4
        e5 = s5 + path_days[5] - 1
        
        s6 = 16
        e6 = 17
        s7 = 17
        e7 = 20
        
        path = [
            (path_cities[0], s0, e0),
            (path_cities[1], s1, e1),
            (path_cities[2], s2, e2),
            (path_cities[3], s3, e3),
            (path_cities[4], s4, e4),
            (path_cities[5], s5, e5),
            ('Oslo', s6, e6),
            ('Frankfurt', s7, e7)
        ]
        
        itinerary = []
        for idx, (city, start, end) in enumerate(path):
            if start == end:
                range_str = f"Day {start}"
            else:
                range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": range_str, "place": city})
            
            if idx < 7:
                itinerary.append({"day_range": f"Day {end}", "place": city})
                next_city = path[idx+1][0]
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()