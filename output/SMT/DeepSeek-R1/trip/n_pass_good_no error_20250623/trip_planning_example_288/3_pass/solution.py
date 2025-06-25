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
        
        blocks = []
        i = 0
        while i < n_days:
            if start_vals[i] == end_vals[i]:
                current_city = start_vals[i]
                j = i
                while j < n_days and start_vals[j] == end_vals[j] and start_vals[j] == current_city:
                    j += 1
                start_day = i + 1
                end_day = j
                if start_day == end_day:
                    day_range_str = f"Day {start_day}"
                else:
                    day_range_str = f"Day {start_day}-{end_day}"
                blocks.append({
                    'day_range': day_range_str,
                    'place': city_names[current_city]
                })
                i = j
            else:
                i += 1
        
        flight_records = []
        for idx in range(n_days):
            if start_vals[idx] != end_vals[idx]:
                flight_records.append({
                    'day_range': f'Day {idx+1}',
                    'place': city_names[start_vals[idx]]
                })
                flight_records.append({
                    'day_range': f'Day {idx+1}',
                    'place': city_names[end_vals[idx]]
                })
        
        events = []
        for block in blocks:
            s = block['day_range']
            if s.startswith('Day '):
                parts = s.split()[1]
                if '-' in parts:
                    start_day = int(parts.split('-')[0])
                else:
                    start_day = int(parts)
                events.append((start_day, block))
        
        for flight in flight_records:
            s = flight['day_range']
            day_num = int(s.split()[1])
            events.append((day_num, flight))
        
        events.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in events]
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()