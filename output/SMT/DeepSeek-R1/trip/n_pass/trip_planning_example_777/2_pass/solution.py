import z3
import json

def main():
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    n_cities = len(cities)
    n_days = 15
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    edges = [
        ('Helsinki', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Helsinki'),
        ('Riga', 'Dublin'),
        ('Vienna', 'Riga'),
        ('Reykjavik', 'Vienna'),
        ('Helsinki', 'Dublin'),
        ('Tallinn', 'Dublin'),
        ('Reykjavik', 'Helsinki'),
        ('Reykjavik', 'Dublin'),
        ('Helsinki', 'Tallinn'),
        ('Vienna', 'Dublin')
    ]
    allowed_edges_set = set()
    for (u, v) in edges:
        u_idx = city_to_index[u]
        v_idx = city_to_index[v]
        allowed_edges_set.add((u_idx, v_idx))
        allowed_edges_set.add((v_idx, u_idx))
    
    start_city = z3.Int('start_city')
    loc = [z3.Int(f'loc_{i}') for i in range(n_days)]
    flight_taken = [z3.Bool(f'flight_taken_{i}') for i in range(n_days)]
    
    optimizer = z3.Optimize()
    
    optimizer.add(start_city >= 0, start_city < n_cities)
    for i in range(n_days):
        optimizer.add(loc[i] >= 0, loc[i] < n_cities)
    
    optimizer.add(z3.Implies(flight_taken[0], loc[0] != start_city))
    optimizer.add(z3.Implies(z3.Not(flight_taken[0]), loc[0] == start_city))
    optimizer.add(z3.Implies(flight_taken[0], 
                             z3.Or([z3.And(start_city == u, loc[0] == v) for (u, v) in allowed_edges_set])))
    
    for i in range(1, n_days):
        optimizer.add(z3.Implies(flight_taken[i], loc[i] != loc[i-1]))
        optimizer.add(z3.Implies(z3.Not(flight_taken[i]), loc[i] == loc[i-1]))
        optimizer.add(z3.Implies(flight_taken[i], 
                                 z3.Or([z3.And(loc[i-1] == u, loc[i] == v) for (u, v) in allowed_edges_set])))
    
    total_days = [0] * n_cities
    in_day1_list = []
    for c in range(n_cities):
        in_start = (start_city == c)
        in_arrival_day1 = z3.And(flight_taken[0], loc[0] == c)
        in_day1 = z3.Or(in_start, in_arrival_day1)
        in_day1_list.append(in_day1)
    
    for c in range(n_cities):
        total_days[c] = z3.If(in_day1_list[c], 1, 0)
        for i in range(1, n_days):
            in_city = z3.Or(loc[i] == c, z3.And(flight_taken[i], loc[i-1] == c))
            total_days[c] = total_days[c] + z3.If(in_city, 1, 0)
    
    optimizer.add(total_days[city_to_index['Dublin']] == 5)
    optimizer.add(total_days[city_to_index['Helsinki']] == 3)
    optimizer.add(total_days[city_to_index['Riga']] == 3)
    optimizer.add(total_days[city_to_index['Reykjavik']] == 2)
    optimizer.add(total_days[city_to_index['Vienna']] == 2)
    optimizer.add(total_days[city_to_index['Tallinn']] == 5)
    
    day3_hel = z3.Or(loc[2] == city_to_index['Helsinki'], z3.And(flight_taken[2], loc[1] == city_to_index['Helsinki']))
    day4_hel = z3.Or(loc[3] == city_to_index['Helsinki'], z3.And(flight_taken[3], loc[2] == city_to_index['Helsinki']))
    day5_hel = z3.Or(loc[4] == city_to_index['Helsinki'], z3.And(flight_taken[4], loc[3] == city_to_index['Helsinki']))
    optimizer.add(z3.Or(day3_hel, day4_hel, day5_hel))
    
    day2_vie = z3.Or(loc[1] == city_to_index['Vienna'], z3.And(flight_taken[1], loc[0] == city_to_index['Vienna']))
    day3_vie = z3.Or(loc[2] == city_to_index['Vienna'], z3.And(flight_taken[2], loc[1] == city_to_index['Vienna']))
    optimizer.add(day2_vie, day3_vie)
    
    tallinn_days = []
    for d in range(6, 11):  # days 7 to 11 (0-indexed days 6 to 10)
        in_day = z3.Or(loc[d] == city_to_index['Tallinn'], z3.And(flight_taken[d], loc[d-1] == city_to_index['Tallinn']))
        tallinn_days.append(in_day)
    optimizer.add(z3.Or(tallinn_days))
    
    num_flights = z3.Sum([z3.If(ft, 1, 0) for ft in flight_taken])
    optimizer.minimize(num_flights)
    
    if optimizer.check() == z3.sat:
        model = optimizer.model()
        start_city_val = model.evaluate(start_city).as_long()
        loc_vals = [model.evaluate(loc[i]).as_long() for i in range(n_days)]
        flight_taken_vals = [model.evaluate(flight_taken[i], model_completion=True) for i in range(n_days)]
        flight_taken_vals = [z3.is_true(ft) for ft in flight_taken_vals]
        
        itinerary = []
        day1_cities = set()
        day1_cities.add(cities[start_city_val])
        if flight_taken_vals[0] and loc_vals[0] != start_city_val:
            day1_cities.add(cities[loc_vals[0]])
        for city_name in day1_cities:
            itinerary.append({"day": 1, "place": city_name})
        
        for d in range(2, n_days+1):
            day_cities = set()
            idx_day = d - 1
            day_cities.add(cities[loc_vals[idx_day]])
            if flight_taken_vals[idx_day] and loc_vals[idx_day] != loc_vals[idx_day-1]:
                day_cities.add(cities[loc_vals[idx_day-1]])
            for city_name in day_cities:
                itinerary.append({"day": d, "place": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()