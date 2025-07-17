from z3 import *
import json

def main():
    # Cities and their indices
    Cities = ["Zurich", "Hamburg", "Helsinki", "Bucharest", "Split"]
    mapping = {city: idx for idx, city in enumerate(Cities)}
    n_cities = len(Cities)
    n_days = 12
    
    # Required days per city
    required_days = [3, 2, 2, 2, 7]  # Zurich, Hamburg, Helsinki, Bucharest, Split
    
    # Direct flights setup
    pairs = [("Zurich", "Helsinki"), ("Hamburg", "Bucharest"), ("Helsinki", "Hamburg"),
             ("Zurich", "Hamburg"), ("Zurich", "Bucharest"), ("Zurich", "Split"),
             ("Helsinki", "Split"), ("Split", "Hamburg")]
    allowed_flights = set()
    for (a, b) in pairs:
        u = mapping[a]
        v = mapping[b]
        allowed_flights.add((u, v))
        allowed_flights.add((v, u))
    
    # Create Z3 variables
    L = [Int(f'L_{i}') for i in range(n_days)]  # L[i] for day i+1 start location
    F = [Int(f'F_{i}') for i in range(n_days-1)]  # F[i] for flight at end of day i+1
    
    s = Solver()
    
    # Constrain L and F to valid city indices
    for i in range(n_days):
        s.add(And(L[i] >= 0, L[i] < n_cities))
    for i in range(n_days-1):
        s.add(And(F[i] >= 0, F[i] < n_cities))
    
    # Flight constraints: if flight is taken, it must be between connected cities and not to the same city
    for i in range(n_days-1):
        s.add(If(F[i] == 0, 
                 True, 
                 And(F[i] != L[i], 
                     Or([And(L[i] == u, F[i] == v) for (u, v) in allowed_flights]))
                ))
    
    # Next day location constraint
    for i in range(n_days-1):
        s.add(If(F[i] == 0, L[i+1] == L[i], L[i+1] == F[i]))
    
    # Presence matrix: present[d][c] is True if we are in city c on day d (0-indexed day d = day d+1)
    present = [[Bool(f'present_{i}_{j}') for j in range(n_cities)] for i in range(n_days)]
    
    # Define presence for days 0 to 10 (day1 to day11)
    for d in range(n_days-1):  # d from 0 to 10 (11 days: day1 to day11)
        for c in range(n_cities):
            # present[d][c] = (L[d] == c) OR (F[d] != 0 and F[d] == c)
            s.add(present[d][c] == Or(L[d] == c, And(F[d] != 0, F[d] == c)))
    # For last day (day12, index11): no flight after, so only L[11] matters
    for c in range(n_cities):
        s.add(present[n_days-1][c] == (L[n_days-1] == c))
    
    # Total days per city constraint
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            total += If(present[d][c], 1, 0)
        s.add(total == required_days[c])
    
    # Special constraints
    # Wedding in Zurich (city0) between day1 and day3: at least one of present[0][0], present[1][0], present[2][0] is true
    s.add(Or(present[0][0], present[1][0], present[2][0]))
    # Conference in Split (city4) on day4 (index3) and day10 (index9)
    s.add(present[3][4])
    s.add(present[9][4])
    
    # Exactly 4 flights
    flight_count = Sum([If(F[i] != 0, 1, 0) for i in range(n_days-1)])
    s.add(flight_count == 4)
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        
        # Extract values for L and F
        L_val = [model.evaluate(L[i]).as_long() for i in range(n_days)]
        F_val = [model.evaluate(F[i]).as_long() for i in range(n_days-1)]
        
        # Build presence matrix values for output
        present_val = [[False]*n_cities for _ in range(n_days)]
        for d in range(n_days):
            for c in range(n_cities):
                if d < n_days-1:
                    if (model.evaluate(present[d][c])).__bool__():
                        present_val[d][c] = True
                else:
                    if (model.evaluate(present[d][c])).__bool__():
                        present_val[d][c] = True
        
        # For each city, get the set of days (1-indexed) where it is present
        city_days = [[] for _ in range(n_cities)]
        for d in range(n_days):
            day_index_1_indexed = d + 1
            for c in range(n_cities):
                if present_val[d][c]:
                    city_days[c].append(day_index_1_indexed)
        
        # Build contiguous intervals for each city
        intervals = []
        for c in range(n_cities):
            days = sorted(city_days[c])
            if not days:
                continue
            current_start = days[0]
            current_end = days[0]
            for i in range(1, len(days)):
                if days[i] == current_end + 1:
                    current_end = days[i]
                else:
                    intervals.append((current_start, current_end, Cities[c]))
                    current_start = days[i]
                    current_end = days[i]
            intervals.append((current_start, current_end, Cities[c]))
        
        # Create records for contiguous intervals
        records = []
        for (start, end, city) in intervals:
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            record = {"day_range": day_range_str, "place": city}
            key = (start, 1, end, city)  # 1 for contiguous segment
            records.append((key, record))
        
        # Create records for flight days
        for d in range(1, 12):  # d: flight day (1-indexed, from 1 to 11)
            idx = d - 1  # index in F_val
            if F_val[idx] != 0:
                dep_city_idx = L_val[idx]
                dep_city = Cities[dep_city_idx]
                arr_city_idx = F_val[idx]
                arr_city = Cities[arr_city_idx]
                # Two records: one for departure city, one for arrival city
                record_dep = {"day_range": f"Day {d}", "place": dep_city}
                key_dep = (d, 0, d, dep_city)  # 0 for flight record
                records.append((key_dep, record_dep))
                record_arr = {"day_range": f"Day {d}", "place": arr_city}
                key_arr = (d, 0, d, arr_city)
                records.append((key_arr, record_arr))
        
        # Sort records: by start day (first element of key), then by type (0: flight record, 1: contiguous segment), then by end day, then by city
        records_sorted = sorted(records, key=lambda x: (x[0][0], x[0][1], x[0][2], x[0][3]))
        itinerary_list = [record for (key, record) in records_sorted]
        
        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()