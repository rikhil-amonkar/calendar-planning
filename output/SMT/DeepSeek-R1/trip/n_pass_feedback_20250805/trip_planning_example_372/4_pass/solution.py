import z3
import json

def main():
    n_days = 13
    cities = {"Madrid": 0, "Porto": 1, "Seville": 2, "Stuttgart": 3}
    inv_cities = {v: k for k, v in cities.items()}
    
    s = z3.Solver()
    
    start = [z3.Int(f'start_{i}') for i in range(n_days)]
    flight = [z3.Bool(f'flight_{i}') for i in range(n_days)]
    end = [z3.Int(f'end_{i}') for i in range(n_days)]
    
    def is_direct(a, b):
        return z3.Or(
            z3.And(a == 1, b == 3), z3.And(a == 3, b == 1),
            z3.And(a == 2, b == 1), z3.And(a == 1, b == 2),
            z3.And(a == 0, b == 1), z3.And(a == 1, b == 0),
            z3.And(a == 0, b == 2), z3.And(a == 2, b == 0)
        )
    
    for i in range(n_days):
        s.add(z3.Or([start[i] == cities[c] for c in cities]))
        s.add(z3.Or([end[i] == cities[c] for c in cities]))
        s.add(z3.Implies(flight[i], start[i] != end[i]))
        s.add(z3.Implies(flight[i], is_direct(start[i], end[i])))
        s.add(z3.Implies(z3.Not(flight[i]), start[i] == end[i]))
    
    for i in range(n_days - 1):
        s.add(end[i] == start[i+1])
    
    total_flights = z3.Sum([z3.If(flight[i], 1, 0) for i in range(n_days)])
    s.add(total_flights == 3)
    
    total_days = [0] * len(cities)
    for c in cities.values():
        count_start = z3.Sum([z3.If(start[i] == c, 1, 0) for i in range(n_days)])
        count_end_flight = z3.Sum([z3.If(z3.And(flight[i], end[i] == c), 1, 0) for i in range(n_days)])
        total_days[c] = count_start + count_end_flight
    
    s.add(total_days[cities["Madrid"]] == 4)
    s.add(total_days[cities["Porto"]] == 3)
    s.add(total_days[cities["Seville"]] == 2)
    s.add(total_days[cities["Stuttgart"]] == 7)
    
    s.add(z3.Or(start[6] == cities["Stuttgart"], z3.And(flight[6], end[6] == cities["Stuttgart"])))
    s.add(z3.Or(start[12] == cities["Stuttgart"], z3.And(flight[12], end[12] == cities["Stuttgart"])))
    
    conditions = []
    for i in range(4):
        conditions.append(start[i] == cities["Madrid"])
        conditions.append(z3.And(flight[i], end[i] == cities["Madrid"]))
    s.add(z3.Or(conditions))
    
    if s.check() == z3.sat:
        m = s.model()
        start_vals = [m.evaluate(start[i]) for i in range(n_days)]
        flight_vals = [m.evaluate(flight[i]) for i in range(n_days)]
        end_vals = [m.evaluate(end[i]) for i in range(n_days)]
        
        days_in_city = {city: [] for city in cities}
        
        for i in range(n_days):
            day_num = i + 1
            start_city = inv_cities[int(str(start_vals[i]))]
            days_in_city[start_city].append(day_num)
            if z3.is_true(flight_vals[i]):
                end_city = inv_cities[int(str(end_vals[i]))]
                days_in_city[end_city].append(day_num)
        
        intervals = []
        for city, days in days_in_city.items():
            if not days:
                continue
            days.sort()
            current_start = days[0]
            for j in range(1, len(days)):
                if days[j] != days[j-1] + 1:
                    intervals.append((current_start, days[j-1], city))
                    current_start = days[j]
            intervals.append((current_start, days[-1], city))
        
        intervals.sort(key=lambda x: x[0])
        
        itinerary = []
        for start_day, end_day, city in intervals:
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()