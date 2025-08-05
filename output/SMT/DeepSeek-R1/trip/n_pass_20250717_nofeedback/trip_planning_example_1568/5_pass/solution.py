import z3

def main():
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    n_cities = len(cities)
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    connections_str = "Riga and Stockholm, Stockholm and Brussels, Istanbul and Munich, Istanbul and Riga, Prague and Split, Vienna and Brussels, Vienna and Riga, Split and Stockholm, Munich and Amsterdam, Split and Amsterdam, Amsterdam and Stockholm, Amsterdam and Riga, Vienna and Stockholm, Vienna and Istanbul, Vienna and Seville, Istanbul and Amsterdam, Munich and Brussels, Prague and Munich, from Riga to Munich, Prague and Amsterdam, Prague and Brussels, Prague and Istanbul, Istanbul and Stockholm, Vienna and Prague, Munich and Split, Vienna and Amsterdam, Prague and Stockholm, Brussels and Seville, Munich and Stockholm, Istanbul and Brussels, Amsterdam and Seville, Vienna and Split, Munich and Seville, Riga and Brussels, Prague and Riga, Vienna and Munich"
    
    tokens = [t.strip() for t in connections_str.split(',')]
    direct_flights_set = set()
    for token in tokens:
        if token.startswith('from'):
            parts = token.split()
            if len(parts) >= 4:
                city1 = parts[1]
                city2 = parts[3]
                direct_flights_set.add(frozenset([city1, city2]))
        else:
            if ' and ' in token:
                parts = token.split(' and ')
                city1 = parts[0]
                city2 = parts[1]
                direct_flights_set.add(frozenset([city1, city2]))
    
    edge_matrix = [[False] * n_cities for _ in range(n_cities)]
    for pair in direct_flights_set:
        lst = list(pair)
        if len(lst) < 2:
            continue
        c1 = lst[0]
        c2 = lst[1]
        if c1 in city_to_int and c2 in city_to_int:
            i1 = city_to_int[c1]
            i2 = city_to_int[c2]
            edge_matrix[i1][i2] = True
            edge_matrix[i2][i1] = True
    
    allowed_pairs = []
    for i in range(n_cities):
        for j in range(n_cities):
            if edge_matrix[i][j]:
                allowed_pairs.append((i, j))
    
    n_days = 20
    end_city = [z3.Int(f'end_city_{i}') for i in range(0, n_days+1)]
    fly = [z3.Bool(f'fly_{d}') for d in range(1, n_days+1)]
    
    s = z3.Solver()
    
    for i in range(0, n_days+1):
        s.add(z3.And(end_city[i] >= 0, end_city[i] < n_cities))
    
    for d in range(1, n_days+1):
        no_fly_cond = (end_city[d] == end_city[d-1])
        if allowed_pairs:
            fly_cond = z3.Or([z3.And(end_city[d-1] == i, end_city[d] == j) for (i, j) in allowed_pairs])
        else:
            fly_cond = z3.BoolVal(False)
        s.add(z3.Implies(z3.Not(fly[d-1]), no_fly_cond))
        s.add(z3.Implies(fly[d-1], fly_cond))
    
    in_city = [[z3.Bool(f'in_{d}_{c}') for c in range(n_cities)] for d in range(1, n_days+1)]
    for d in range(1, n_days+1):
        for c in range(n_cities):
            not_flying_cond = z3.And(z3.Not(fly[d-1]), end_city[d] == c)
            flying_cond = z3.And(fly[d-1], z3.Or(end_city[d-1] == c, end_city[d] == c))
            s.add(in_city[d-1][c] == z3.Or(not_flying_cond, flying_cond))
    
    total_days = [z3.Int(f'total_{city}') for city in cities]
    for c in range(n_cities):
        s.add(total_days[c] == z3.Sum([z3.If(in_city[d][c], 1, 0) for d in range(0, n_days)]))
    
    s.add(total_days[city_to_int['Prague']] == 5)
    s.add(total_days[city_to_int['Brussels']] == 2)
    s.add(total_days[city_to_int['Riga']] == 2)
    s.add(total_days[city_to_int['Munich']] == 2)
    s.add(total_days[city_to_int['Seville']] == 3)
    s.add(total_days[city_to_int['Stockholm']] == 2)
    s.add(total_days[city_to_int['Istanbul']] == 2)
    s.add(total_days[city_to_int['Amsterdam']] == 3)
    s.add(total_days[city_to_int['Vienna']] == 5)
    s.add(total_days[city_to_int['Split']] == 3)
    
    # Fixed events - Prague show days 5-9
    for d in [5,6,7,8,9]:
        s.add(in_city[d-1][city_to_int['Prague']] == True)
    
    # No flights during Prague event (days 5-9)
    for d in [5,6,7,8,9]:
        s.add(fly[d-1] == False)
        s.add(end_city[d] == city_to_int['Prague'])
    
    # Must be in Prague by end of day 4
    s.add(end_city[4] == city_to_int['Prague'])
    
    # Riga on day 15 or 16
    s.add(z3.Or(in_city[15-1][city_to_int['Riga']], in_city[16-1][city_to_int['Riga']]))
    
    # Vienna in first five days
    vienna_days = [in_city[d-1][city_to_int['Vienna']] for d in [1,2,3,4,5]]
    s.add(z3.Or(vienna_days))
    
    # Split on days 11-13
    for d in [11,12,13]:
        s.add(in_city[d-1][city_to_int['Split']] == True)
    
    # Stockholm on days 16-17
    s.add(in_city[16-1][city_to_int['Stockholm']] == True)
    s.add(in_city[17-1][city_to_int['Stockholm']] == True)
    
    if s.check() == z3.sat:
        m = s.model()
        end_city_vals = [m.eval(end_city[i]).as_long() for i in range(0, n_days+1)]
        fly_vals = [m[fly[d]] for d in range(0, n_days)]
        
        itinerary = []
        for d in range(1, n_days+1):
            if fly_vals[d-1]:
                city1 = int_to_city[end_city_vals[d-1]]
                city2 = int_to_city[end_city_vals[d]]
                location_str = f"{city1} and {city2}"
            else:
                location_str = int_to_city[end_city_vals[d]]
            itinerary.append({"day": d, "location": location_str})
        
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()