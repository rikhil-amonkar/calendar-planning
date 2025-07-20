from z3 import *
import json

def main():
    n_days = 16
    cities = ['London', 'Oslo', 'Porto', 'Split']
    # Define direct flight edges (as unordered pairs)
    direct_edges = { (0,1), (1,3), (1,2), (0,3) }  # indices: 0:London, 1:Oslo, 2:Porto, 3:Split
    # Build list of allowed flight pairs (both directions)
    allowed_pairs = []
    for a in range(4):
        for b in range(4):
            if a != b and (min(a,b), max(a,b)) in direct_edges:
                allowed_pairs.append((a, b))
    
    # Z3 variables
    flight = [None]  # index 0 unused; flight[1] to flight[16]
    city_start = [None]  # city_start[1] to city_start[16]
    city_end = [None]    # city_end[1] to city_end[16]
    
    for i in range(1, n_days+1):
        flight.append(Bool(f'flight_{i}'))
        city_start.append(Int(f'cs_{i}'))
        city_end.append(Int(f'ce_{i}'))
    
    s = Solver()
    
    # Domain constraints for city_start and city_end
    for i in range(1, n_days+1):
        s.add(Or([city_start[i] == c for c in range(4)]))
        s.add(Or([city_end[i] == c for c in range(4)]))
    
    # Flight constraints
    for i in range(1, n_days+1):
        # If no flight, start and end are the same
        s.add(If(flight[i],
                 And(city_start[i] != city_end[i],
                     Or([And(city_start[i] == a, city_end[i] == b) for (a,b) in allowed_pairs])),
                 city_start[i] == city_end[i]
                ))
    
    # Chain: end of day i must equal start of day i+1
    for i in range(1, n_days):
        s.add(city_end[i] == city_start[i+1])
    
    # Show in Split: must be in Split on days 7-11 (inclusive)
    for d in range(7, 12):
        s.add(Or(city_start[d] == 3, city_end[d] == 3))
    
    # Relatives in London: must be in London on at least one day between 1 and 7
    s.add(Or([Or(city_start[d] == 0, city_end[d] == 0) for d in range(1, 8)]))
    
    # Total days per city
    total_london = 0
    total_oslo = 0
    total_porto = 0
    total_split = 0
    
    for i in range(1, n_days+1):
        # Count city_start[i] for the city
        # For flight days, also count city_end[i] for the arrival city
        # Formula: total = (# days i: city_start[i]==c) + (# flight days i: city_end[i]==c)
        total_london += If(city_start[i] == 0, 1, 0) + If(And(flight[i], city_end[i] == 0), 1, 0)
        total_oslo   += If(city_start[i] == 1, 1, 0) + If(And(flight[i], city_end[i] == 1), 1, 0)
        total_porto  += If(city_start[i] == 2, 1, 0) + If(And(flight[i], city_end[i] == 2), 1, 0)
        total_split  += If(city_start[i] == 3, 1, 0) + If(And(flight[i], city_end[i] == 3), 1, 0)
    
    s.add(total_london == 7)
    s.add(total_oslo == 2)
    s.add(total_porto == 5)
    s.add(total_split == 5)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        flight_val = [None]  # flight_val[i] for i in 1..16
        city_start_val = [None]
        city_end_val = [None]
        
        for i in range(1, n_days+1):
            flight_val.append(is_true(m[flight[i]]))
            city_start_val.append(m[city_start[i]].as_long())
            city_end_val.append(m[city_end[i]].as_long())
        
        # Build itinerary records
        records = []  # list of (first_day, type, record_dict)
        # Type: 0 for flight record, 1 for continuous stay
        
        # Step 1: Continuous stays per city
        for c_index in range(4):
            city_name = cities[c_index]
            days_in_city = set()
            for day in range(1, n_days+1):
                if city_start_val[day] == c_index or city_end_val[day] == c_index:
                    days_in_city.add(day)
            
            if not days_in_city:
                continue
            sorted_days = sorted(days_in_city)
            intervals = []
            start = sorted_days[0]
            end = start
            for d in sorted_days[1:]:
                if d == end + 1:
                    end = d
                else:
                    intervals.append((start, end))
                    start = d
                    end = d
            intervals.append((start, end))
            
            for (s_day, e_day) in intervals:
                if s_day == e_day:
                    day_range_str = f"Day {s_day}"
                else:
                    day_range_str = f"Day {s_day}-{e_day}"
                record = {"day_range": day_range_str, "place": city_name}
                records.append((s_day, 1, record))
        
        # Step 2: Flight records
        for day in range(1, n_days+1):
            if flight_val[day]:
                dep_city = cities[city_start_val[day]]
                arr_city = cities[city_end_val[day]]
                record_dep = {"day_range": f"Day {day}", "place": dep_city}
                record_arr = {"day_range": f"Day {day}", "place": arr_city}
                records.append((day, 0, record_dep))
                records.append((day, 0, record_arr))
        
        # Sort records: by first_day (ascending) and by type (0 before 1)
        records.sort(key=lambda x: (x[0], x[1]))
        itinerary_list = [rec for (_, _, rec) in records]
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()