import z3
import json

def main():
    cities = ["Prague", "Warsaw", "Dublin", "Athens", "Vilnius", "Porto", "London", "Seville", "Lisbon", "Dubrovnik"]
    n_cities = len(cities)
    n_days = 26
    
    direct_flights = [
        (1,4), (0,3), (6,8), (8,5), (0,8), (6,2), (3,4), (3,2), (0,6), (6,1),
        (2,7), (7,5), (8,3), (2,5), (3,1), (8,1), (5,1), (0,1), (0,2), (3,9),
        (8,2), (9,2), (8,7), (6,3)
    ]
    direct_flights_set = set(direct_flights)
    
    s = z3.Solver()
    
    start_city = [z3.Int(f"start_city_{i}") for i in range(1, n_days+1)]
    end_city = [z3.Int(f"end_city_{i}") for i in range(1, n_days+1)]
    
    for i in range(n_days):
        s.add(z3.And(start_city[i] >= 0, start_city[i] < n_cities))
        s.add(z3.And(end_city[i] >= 0, end_city[i] < n_cities))
    
    for i in range(n_days-1):
        s.add(end_city[i] == start_city[i+1])
    
    for i in range(n_days):
        city_start = start_city[i]
        city_end = end_city[i]
        flight_taken = (city_start != city_end)
        allowed_flight = z3.BoolVal(False)
        for (a, b) in direct_flights_set:
            allowed_flight = z3.Or(allowed_flight,
                                   z3.And(city_start == a, city_end == b),
                                   z3.And(city_start == b, city_end == a))
        s.add(z3.Implies(flight_taken, allowed_flight))
    
    s.add(z3.Or(start_city[0] == 0, end_city[0] == 0))
    s.add(z3.Or(start_city[1] == 0, end_city[1] == 0))
    s.add(z3.Or(start_city[2] == 0, end_city[2] == 0))
    s.add(z3.Or(start_city[2] == 6, end_city[2] == 6))
    s.add(z3.Or(start_city[3] == 6, end_city[3] == 6))
    s.add(z3.Or(start_city[4] == 6, end_city[4] == 6))
    s.add(z3.Or(start_city[4] == 8, end_city[4] == 8))
    s.add(z3.Or(start_city[5] == 8, end_city[5] == 8))
    s.add(z3.Or(start_city[6] == 8, end_city[6] == 8))
    s.add(z3.Or(start_city[7] == 8, end_city[7] == 8))
    s.add(z3.Or(start_city[8] == 8, end_city[8] == 8))
    s.add(z3.Or(start_city[15] == 5, end_city[15] == 5))
    s.add(z3.Or(start_city[16] == 5, end_city[16] == 5))
    s.add(z3.Or(start_city[17] == 5, end_city[17] == 5))
    s.add(z3.Or(start_city[18] == 5, end_city[18] == 5))
    s.add(z3.Or(start_city[19] == 5, end_city[19] == 5))
    s.add(z3.Or(start_city[19] == 1, end_city[19] == 1))
    s.add(z3.Or(start_city[20] == 1, end_city[20] == 1))
    s.add(z3.Or(start_city[21] == 1, end_city[21] == 1))
    s.add(z3.Or(start_city[22] == 1, end_city[22] == 1))
    
    required_days_list = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]
    for c in range(n_cities):
        total_days = 0
        for i in range(n_days):
            present = z3.Or(start_city[i] == c, end_city[i] == c)
            total_days += z3.If(present, 1, 0)
        s.add(total_days == required_days_list[c])
    
    if s.check() == z3.sat:
        m = s.model()
        days_per_city = [[] for _ in range(n_cities)]
        for i in range(n_days):
            day_num = i + 1
            start_val = m.evaluate(start_city[i]).as_long()
            end_val = m.evaluate(end_city[i]).as_long()
            days_per_city[start_val].append(day_num)
            if start_val != end_val:
                days_per_city[end_val].append(day_num)
        
        itinerary_list = []
        for c in range(n_cities):
            days = sorted(days_per_city[c])
            if not days:
                continue
            current_start = days[0]
            current_end = days[0]
            for j in range(1, len(days)):
                if days[j] == current_end + 1:
                    current_end = days[j]
                else:
                    if current_start == current_end:
                        day_range = f"Day {current_start}"
                    else:
                        day_range = f"Day {current_start}-{current_end}"
                    itinerary_list.append({"day_range": day_range, "place": cities[c]})
                    current_start = days[j]
                    current_end = days[j]
            if current_start == current_end:
                day_range = f"Day {current_start}"
            else:
                day_range = f"Day {current_start}-{current_end}"
            itinerary_list.append({"day_range": day_range, "place": cities[c]})
        
        def get_first_day(entry):
            parts = entry['day_range'].replace('Day ', '').split('-')
            return int(parts[0])
        
        itinerary_list.sort(key=get_first_day)
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()