from z3 import *

def main():
    manchester = 0
    madrid = 1
    stuttgart = 2
    vienna = 3
    city_names = {
        manchester: "Manchester",
        madrid: "Madrid",
        stuttgart: "Stuttgart",
        vienna: "Vienna"
    }
    
    allowed_directed = [
        (manchester, madrid),
        (madrid, manchester),
        (manchester, stuttgart),
        (stuttgart, manchester),
        (manchester, vienna),
        (vienna, manchester),
        (madrid, vienna),
        (vienna, madrid),
        (stuttgart, vienna),
        (vienna, stuttgart)
    ]
    
    n_days = 15
    city_start = [Int(f'city_start_{i}') for i in range(n_days)]
    city_end = [Int(f'city_end_{i}') for i in range(n_days)]
    
    s = Solver()
    
    for i in range(n_days):
        s.add(And(city_start[i] >= 0, city_start[i] <= 3))
        s.add(And(city_end[i] >= 0, city_end[i] <= 3))
    
    for i in range(n_days - 1):
        s.add(city_end[i] == city_start[i+1])
    
    for i in range(n_days):
        no_flight = (city_start[i] == city_end[i])
        flight_conds = []
        for (a, b) in allowed_directed:
            flight_conds.append(And(city_start[i] == a, city_end[i] == b))
        flight_cond = Or(flight_conds)
        s.add(Or(no_flight, flight_cond))
    
    def count_days(c):
        total = 0
        for i in range(n_days):
            total += If(city_start[i] == c, 1, 0)
            total += If(And(city_end[i] == c, city_start[i] != c), 1, 0)
        return total
    
    s.add(count_days(manchester) == 7)
    s.add(count_days(madrid) == 4)
    s.add(count_days(stuttgart) == 5)
    s.add(count_days(vienna) == 2)
    
    manchester_event = []
    for i in range(0, 7):
        manchester_event.append(And(city_start[i] == manchester, city_end[i] == manchester))
    s.add(Or(manchester_event))
    
    stuttgart_event = []
    for i in range(10, 15):
        stuttgart_event.append(And(city_start[i] == stuttgart, city_end[i] == stuttgart))
    s.add(Or(stuttgart_event))
    
    if s.check() == sat:
        m = s.model()
        start_vals = [m.eval(city_start[i]).as_long() for i in range(n_days)]
        end_vals = [m.eval(city_end[i]).as_long() for i in range(n_days)]
        
        presence = {city: set() for city in city_names.keys()}
        for i in range(n_days):
            s_city = start_vals[i]
            e_city = end_vals[i]
            presence[s_city].add(i)
            if s_city != e_city:
                presence[e_city].add(i)
        
        segments = []
        for city, days_set in presence.items():
            if not days_set:
                continue
            days_list = sorted(days_set)
            i_idx = 0
            while i_idx < len(days_list):
                j_idx = i_idx
                while j_idx < len(days_list) - 1 and days_list[j_idx+1] == days_list[j_idx] + 1:
                    j_idx += 1
                start_day = days_list[i_idx] + 1
                end_day = days_list[j_idx] + 1
                if start_day == end_day:
                    day_range_str = f"Day {start_day}"
                else:
                    day_range_str = f"Day {start_day}-{end_day}"
                segments.append({
                    'day_range': day_range_str,
                    'place': city_names[city]
                })
                i_idx = j_idx + 1
        
        def get_first_day(seg):
            s = seg['day_range']
            parts = s.split()[1]
            if '-' in parts:
                return int(parts.split('-')[0])
            else:
                return int(parts)
        
        segments.sort(key=get_first_day)
        result = {"itinerary": segments}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()