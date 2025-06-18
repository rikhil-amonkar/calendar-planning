import z3
import json

def main():
    cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
    city_index = {city: idx for idx, city in enumerate(cities)}
    index_city = {idx: city for idx, city in enumerate(cities)}
    
    required_days = {
        'Prague': 3,
        'Warsaw': 4,
        'Dublin': 3,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 3,
        'Seville': 2,
        'Lisbon': 5,
        'Dubrovnik': 3
    }
    
    fixed_events = {
        'Prague': [1, 2, 3],
        'London': [3, 4, 5],
        'Lisbon': [5, 6, 7, 8, 9],
        'Porto': [16, 17, 18, 19, 20],
        'Warsaw': [20, 21, 22, 23]
    }
    
    direct_flights_str = "Warsaw and Vilnius, Prague and Athens, London and Lisbon, Lisbon and Porto, Prague and Lisbon, London and Dublin, Athens and Vilnius, Athens and Dublin, Prague and London, London and Warsaw, Dublin and Seville, Seville and Porto, Lisbon and Athens, Dublin and Porto, Athens and Warsaw, Lisbon and Warsaw, Porto and Warsaw, Prague and Warsaw, Prague and Dublin, Athens and Dubrovnik, Lisbon and Dublin, Dubrovnik and Dublin, Lisbon and Seville, London and Athens"
    flight_pairs = []
    for pair in direct_flights_str.split(','):
        pair = pair.strip()
        if pair:
            parts = pair.split(' and ')
            if len(parts) == 2:
                flight_pairs.append((parts[0].strip(), parts[1].strip()))
                
    n = len(cities)
    flight_matrix = [[False] * n for _ in range(n)]
    for (c1, c2) in flight_pairs:
        i1 = city_index[c1]
        i2 = city_index[c2]
        flight_matrix[i1][i2] = True
        flight_matrix[i2][i1] = True
        
    loc = [z3.Int(f'loc_{i}') for i in range(1, 28)]
    
    s = z3.Solver()
    
    for i in range(27):
        s.add(loc[i] >= 0, loc[i] < n)
    
    s.add(loc[0] == city_index['Prague'])
    
    for i in range(1, 27):
        start_city = loc[i-1]
        end_city = loc[i]
        s.add(z3.Implies(start_city != end_city, 
                         flight_matrix[start_city.as_long()][end_city.as_long()] if isinstance(start_city, int) and isinstance(end_city, int) else 
                         z3.Or([z3.And(start_city == idx1, end_city == idx2) for idx1 in range(n) for idx2 in range(n) if flight_matrix[idx1][idx2]])))
    
    for city, days in fixed_events.items():
        c_idx = city_index[city]
        for d in days:
            s.add(z3.Or(loc[d-1] == c_idx, loc[d] == c_idx))
            
    for city in cities:
        total = 0
        c_idx = city_index[city]
        for d in range(1, 27):
            in_city = z3.Or(loc[d-1] == c_idx, loc[d] == c_idx)
            total += z3.If(in_city, 1, 0)
        s.add(total == required_days[city])
        
    if s.check() == z3.sat:
        m = s.model()
        loc_vals = [m.evaluate(loc[i]).as_long() for i in range(27)]
        
        itinerary = []
        
        city_days = {city: [] for city in cities}
        for day in range(1, 27):
            for city in cities:
                c_idx = city_index[city]
                if loc_vals[day-1] == c_idx or loc_vals[day] == c_idx:
                    city_days[city].append(day)
                    
        for city, days_list in city_days.items():
            if not days_list:
                continue
            days_list.sort()
            groups = []
            start = days_list[0]
            end = days_list[0]
            for i in range(1, len(days_list)):
                if days_list[i] == end + 1:
                    end = days_list[i]
                else:
                    groups.append((start, end))
                    start = days_list[i]
                    end = days_list[i]
            groups.append((start, end))
            
            for (s_val, e_val) in groups:
                if s_val == e_val:
                    day_str = f"Day {s_val}"
                else:
                    day_str = f"Day {s_val}-{e_val}"
                itinerary.append({"day_range": day_str, "place": city})
                    
        for day in range(1, 27):
            if loc_vals[day-1] != loc_vals[day]:
                city1 = index_city[loc_vals[day-1]]
                city2 = index_city[loc_vals[day]]
                itinerary.append({"day_range": f"Day {day}", "place": city1})
                itinerary.append({"day_range": f"Day {day}", "place": city2})
                
        def get_start_day(entry):
            parts = entry['day_range'].split()
            num_part = parts[1]
            if '-' in num_part:
                return int(num_part.split('-')[0])
            else:
                return int(num_part)
                
        itinerary_sorted = sorted(itinerary, key=get_start_day)
        result = {"itinerary": itinerary_sorted}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()