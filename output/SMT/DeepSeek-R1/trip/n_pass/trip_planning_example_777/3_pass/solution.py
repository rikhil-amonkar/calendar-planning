import z3
import json
from collections import defaultdict

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
    
    helsinki_idx = city_to_index['Helsinki']
    day3_hel = z3.Or(loc[2] == helsinki_idx, z3.And(flight_taken[2], loc[1] == helsinki_idx))
    day4_hel = z3.Or(loc[3] == helsinki_idx, z3.And(flight_taken[3], loc[2] == helsinki_idx))
    day5_hel = z3.Or(loc[4] == helsinki_idx, z3.And(flight_taken[4], loc[3] == helsinki_idx))
    optimizer.add(z3.Or(day3_hel, day4_hel, day5_hel))
    
    vienna_idx = city_to_index['Vienna']
    day2_vie = z3.Or(loc[1] == vienna_idx, z3.And(flight_taken[1], loc[0] == vienna_idx))
    day3_vie = z3.Or(loc[2] == vienna_idx, z3.And(flight_taken[2], loc[1] == vienna_idx))
    optimizer.add(day2_vie, day3_vie)
    
    tallinn_idx = city_to_index['Tallinn']
    tallinn_days = []
    for d in range(6, 11):  # days 7 to 11 (0-indexed days 6 to 10)
        in_day = z3.Or(loc[d] == tallinn_idx, z3.And(flight_taken[d], loc[d-1] == tallinn_idx))
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
        
        occurrences = []
        day1_cities = set()
        start_city_name = cities[start_city_val]
        occurrences.append((1, start_city_name))
        if flight_taken_vals[0]:
            arrival_city_day1 = cities[loc_vals[0]]
            occurrences.append((1, arrival_city_day1))
        
        for d in range(2, n_days+1):
            idx_day = d - 1
            end_city = cities[loc_vals[idx_day-1]]
            occurrences.append((d, end_city))
            if flight_taken_vals[idx_day-1]:
                start_city_of_day = cities[loc_vals[idx_day-2]] if idx_day-2 >= 0 else cities[start_city_val]
                occurrences.append((d, start_city_of_day))
        
        city_days = defaultdict(list)
        for day, city in occurrences:
            city_days[city].append(day)
        
        itinerary = []
        for city, days_list in city_days.items():
            days_list.sort()
            groups = []
            if not days_list:
                continue
            start_group = days_list[0]
            end_group = days_list[0]
            for i in range(1, len(days_list)):
                if days_list[i] == end_group + 1:
                    end_group = days_list[i]
                else:
                    groups.append((start_group, end_group))
                    start_group = days_list[i]
                    end_group = days_list[i]
            groups.append((start_group, end_group))
            
            for (s, e) in groups:
                if s == e:
                    day_range_str = f"Day {s}"
                else:
                    day_range_str = f"Day {s}-{e}"
                itinerary.append({"day_range": day_range_str, "place": city})
        
        itinerary_sorted = sorted(itinerary, key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0])
        result = {"itinerary": itinerary_sorted}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()