import z3
import json

def main():
    # Define city names and their indices
    cities = ["Prague", "Helsinki", "Frankfurt", "Naples", "Lyon"]
    city_to_index = {name: idx for idx, name in enumerate(cities)}
    
    # Allowed direct flight pairs (symmetric)
    allowed_pairs = [
        (0, 1), (1, 0),  # Prague <-> Helsinki
        (0, 2), (2, 0),  # Prague <-> Frankfurt
        (0, 4), (4, 0),  # Prague <-> Lyon
        (1, 2), (2, 1),  # Helsinki <-> Frankfurt
        (1, 3), (3, 1),  # Helsinki <-> Naples
        (2, 3), (3, 2),  # Frankfurt <-> Naples
        (2, 4), (4, 2)   # Frankfurt <-> Lyon
    ]
    
    # Create Z3 variables for start and end cities for each day (12 days)
    start_city = [z3.Int(f'start_city_{d}') for d in range(12)]
    end_city = [z3.Int(f'end_city_{d}') for d in range(12)]
    
    solver = z3.Solver()
    
    # Fixed constraints for the first 5 days
    # Day 1: Start and end in Prague
    solver.add(start_city[0] == city_to_index["Prague"])
    solver.add(end_city[0] == city_to_index["Prague"])
    # Day 2: Start in Prague, end in Helsinki
    solver.add(start_city[1] == city_to_index["Prague"])
    solver.add(end_city[1] == city_to_index["Helsinki"])
    # Day 3: Start and end in Helsinki
    solver.add(start_city[2] == city_to_index["Helsinki"])
    solver.add(end_city[2] == city_to_index["Helsinki"])
    # Day 4: Start and end in Helsinki
    solver.add(start_city[3] == city_to_index["Helsinki"])
    solver.add(end_city[3] == city_to_index["Helsinki"])
    # Day 5: Start in Helsinki, end in either Naples or Frankfurt
    solver.add(start_city[4] == city_to_index["Helsinki"])
    solver.add(z3.Or(end_city[4] == city_to_index["Naples"], end_city[4] == city_to_index["Frankfurt"]))
    
    # Continuity constraint: Next day's start is the previous day's end
    for d in range(1, 12):
        solver.add(start_city[d] == end_city[d-1])
    
    # Flight constraints: If start and end cities differ, the flight must be allowed
    for d in range(12):
        s = start_city[d]
        e = end_city[d]
        # If start and end are different, check if the flight is allowed
        flight_cond = z3.Or([z3.And(s == a, e == b) for (a, b) in allowed_pairs])
        solver.add(z3.If(s != e, flight_cond, True))
    
    # Total days per city constraints
    total_days = [0] * 5
    for c in range(5):
        total = 0
        for d in range(12):
            total += z3.If(z3.Or(start_city[d] == c, end_city[d] == c), 1, 0)
        solver.add(total == [2, 4, 3, 4, 3][c])
    
    # Solve the problem
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract the start and end cities from the model
        start_vals = [model.evaluate(start_city[d]).as_long() for d in range(12)]
        end_vals = [model.evaluate(end_city[d]).as_long() for d in range(12)]
        
        # Build itinerary records
        records = []
        # For each city, collect the days it is visited
        for c in range(5):
            days_set = set()
            flight_days_set = set()
            for d in range(12):
                day_num = d + 1
                if start_vals[d] == c or end_vals[d] == c:
                    days_set.add(day_num)
                if (start_vals[d] == c and end_vals[d] != c) or (end_vals[d] == c and start_vals[d] != c):
                    flight_days_set.add(day_num)
            
            if not days_set:
                continue
            
            # Form continuous segments (without breaking at flight days)
            sorted_days = sorted(days_set)
            segments = []
            if sorted_days:
                start_seg = sorted_days[0]
                end_seg = sorted_days[0]
                for i in range(1, len(sorted_days)):
                    if sorted_days[i] == end_seg + 1:
                        end_seg = sorted_days[i]
                    else:
                        segments.append((start_seg, end_seg))
                        start_seg = sorted_days[i]
                        end_seg = sorted_days[i]
                segments.append((start_seg, end_seg))
            
            # Add continuous stay records
            for seg in segments:
                s, e = seg
                if s == e:
                    records.append({"day_range": f"Day {s}", "place": cities[c]})
                else:
                    records.append({"day_range": f"Day {s}-{e}", "place": cities[c]})
            
            # Add flight day records
            for d in flight_days_set:
                records.append({"day_range": f"Day {d}", "place": cities[c]})
        
        # Sort records by the start day of the day_range
        def get_start_day(rec):
            s = rec['day_range'].replace('Day ', '')
            if '-' in s:
                return int(s.split('-')[0])
            return int(s)
        
        records_sorted = sorted(records, key=lambda x: (get_start_day(x), x['place'], x['day_range']))
        
        # Output the itinerary as JSON
        result = {"itinerary": records_sorted}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()