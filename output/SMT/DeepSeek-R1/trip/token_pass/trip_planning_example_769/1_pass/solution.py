import z3
import json

def main():
    n_days = 16
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    required_days = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }
    
    direct_flights = [
        ("Porto", "Amsterdam"),
        ("Munich", "Amsterdam"),
        ("Reykjavik", "Amsterdam"),
        ("Munich", "Porto"),
        ("Prague", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Amsterdam", "Santorini"),
        ("Prague", "Amsterdam"),
        ("Prague", "Munich")
    ]
    direct_flights_set = set()
    for (a, b) in direct_flights:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    solver = z3.Solver()
    
    in_city = [[z3.Bool(f"day_{day}_{city}") for city in cities] for day in range(1, n_days+1)]
    
    for day in range(n_days):
        solver.add(z3.AtLeast(*in_city[day], 1))
        solver.add(z3.AtMost(*in_city[day], 2))
    
    for city_idx, city in enumerate(cities):
        total_days = z3.Sum([z3.If(in_city[day][city_idx], 1, 0) for day in range(n_days)])
        solver.add(total_days == required_days[city])
    
    for day in range(n_days):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                solver.add(z3.Implies(
                    z3.And(in_city[day][i], in_city[day][j]),
                    (city_i, city_j) in direct_flights_set
                ))
    
    for day in range(n_days-1):
        common_city = z3.Or([z3.And(in_city[day][i], in_city[day+1][i]) for i in range(len(cities))])
        solver.add(common_city)
    
    reykjavik_idx = cities.index("Reykjavik")
    solver.add(z3.Or([in_city[day][reykjavik_idx] for day in range(3, 7)]))
    
    amsterdam_idx = cities.index("Amsterdam")
    solver.add(in_city[13][amsterdam_idx])
    solver.add(in_city[14][amsterdam_idx])
    
    munich_idx = cities.index("Munich")
    solver.add(z3.Or([in_city[day][munich_idx] for day in range(6, 10)]))
    
    if solver.check() == z3.sat:
        model = solver.model()
        city_days = {city: [] for city in cities}
        for day in range(n_days):
            for city_idx, city in enumerate(cities):
                if z3.is_true(model.evaluate(in_city[day][city_idx])):
                    city_days[city].append(day+1)
        
        segments = []
        for city, days_list in city_days.items():
            if not days_list:
                continue
            days_list.sort()
            start = days_list[0]
            end = days_list[0]
            for day in days_list[1:]:
                if day == end + 1:
                    end = day
                else:
                    segments.append((start, end, city))
                    start = day
                    end = day
            segments.append((start, end, city))
        
        segments.sort(key=lambda x: x[0])
        itinerary_list = []
        for (start, end, city) in segments:
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()