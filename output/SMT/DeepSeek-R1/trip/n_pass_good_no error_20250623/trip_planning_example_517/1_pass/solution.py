from z3 import *
import json

def main():
    # Create the solver
    s = Solver()
    
    # Base for days 1 to 19: base[0] is day1, base[1] is day2, ... base[18] is day19.
    base = [Int('base_%d' % i) for i in range(1, 20)]
    
    # Flight for days 1 to 18: flight[0] is day1, flight[1] is day2, ... flight[17] is day18.
    flight = [Bool('flight_%d' % i) for i in range(1, 19)]
    
    # Allowed city indices: 0=Bucharest, 1=Warsaw, 2=Stuttgart, 3=Copenhagen, 4=Dubrovnik.
    for i in range(19):
        s.add(base[i] >= 0, base[i] <= 4)
    
    # Allowed flight pairs (bidirectional)
    allowed_pairs = set()
    allowed_pairs.add((1, 3)); allowed_pairs.add((3, 1))  # Warsaw and Copenhagen
    allowed_pairs.add((2, 3)); allowed_pairs.add((3, 2))  # Stuttgart and Copenhagen
    allowed_pairs.add((1, 2)); allowed_pairs.add((2, 1))  # Warsaw and Stuttgart
    allowed_pairs.add((0, 3)); allowed_pairs.add((3, 0))  # Bucharest and Copenhagen
    allowed_pairs.add((0, 1)); allowed_pairs.add((1, 0))  # Bucharest and Warsaw
    allowed_pairs.add((3, 4)); allowed_pairs.add((4, 3))  # Copenhagen and Dubrovnik
    
    # Flight constraints for days 1 to 18
    for i in range(18):
        # If flight on day i+1 (flight[i]), then base[i] and base[i+1] must be in allowed_pairs and different.
        # Otherwise, base[i] must equal base[i+1].
        s.add(If(flight[i],
                 And(base[i] != base[i+1],
                     Or([And(base[i] == a, base[i+1] == b) for (a, b) in allowed_pairs])),
                 base[i] == base[i+1]))
    
    # Fixed days: must be in Stuttgart (2) on day7 (base[6]) and day13 (base[12])
    s.add(base[6] == 2)  # base[6] is day7
    s.add(base[12] == 2) # base[12] is day13
    
    # Bucharest constraint: must be in Bucharest (0) on at least one day from 1 to 6.
    # We consider days 1 to 5 (since on day6, if we are in Bucharest, we cannot fly to Stuttgart directly for day7)
    conditions = []
    for i in range(5):  # i from 0 to 4: representing days 1 to 5 (base indices 0 to 4)
        # Either base[i] is Bucharest (0) or we have a flight on day i+1 (flight[i]) landing in Bucharest (base[i+1]==0)
        conditions.append(Or(base[i] == 0, And(flight[i], base[i+1] == 0)))
    s.add(Or(conditions))
    
    # Total flights must be 4
    s.add(Sum([If(flight[i], 1, 0) for i in range(18)]) == 4)
    
    # Total days per city: base_count + flight_land_count (arrival flights)
    city_totals = [6, 2, 7, 3, 5]  # Bucharest, Warsaw, Stuttgart, Copenhagen, Dubrovnik
    for c in range(5):
        base_count = Sum([If(base[i] == c, 1, 0) for i in range(19)])
        flight_land_count = Sum([If(And(flight[i], base[i+1] == c), 1, 0) for i in range(18)])
        total = base_count + flight_land_count
        s.add(total == city_totals[c])
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        base_val = [model.evaluate(base[i]).as_long() for i in range(19)]
        flight_val = [model.evaluate(flight[i]) for i in range(18)]
        
        city_names = {
            0: "Bucharest",
            1: "Warsaw",
            2: "Stuttgart",
            3: "Copenhagen",
            4: "Dubrovnik"
        }
        
        # Step 1: For each city, compute the set of days the traveler is in that city.
        days_in_city = {c: set() for c in range(5)}
        
        # Base days: day i+1 is in city base_val[i]
        for i in range(19):
            c = base_val[i]
            days_in_city[c].add(i+1)  # because i=0 is day1, i=1 is day2, etc.
        
        # Flight arrival days: flight on day i+1 (flight_val[i]) lands in base_val[i+1] on day i+1
        for i in range(18):
            if flight_val[i]:
                arrival_city = base_val[i+1]
                days_in_city[arrival_city].add(i+1)  # flight on day i+1
        
        # Step 2: For each city, group consecutive days into blocks.
        itinerary_records = []
        for c in range(5):
            if not days_in_city[c]:
                continue
            days = sorted(days_in_city[c])
            blocks = []
            start = days[0]
            end = days[0]
            for day in days[1:]:
                if day == end + 1:
                    end = day
                else:
                    if start == end:
                        blocks.append((start, start))
                    else:
                        blocks.append((start, end))
                    start = day
                    end = day
            if start == end:
                blocks.append((start, start))
            else:
                blocks.append((start, end))
            
            for (s_day, e_day) in blocks:
                if s_day == e_day:
                    day_range_str = f"Day {s_day}"
                else:
                    day_range_str = f"Day {s_day}-{e_day}"
                itinerary_records.append({
                    'day_range': day_range_str,
                    'place': city_names[c],
                    'type': 1,  # block record
                    'first_day': s_day
                })
        
        # Step 3: Flight records: for each flight day, two records
        for i in range(18):
            if flight_val[i]:
                day_num = i+1
                dep_city = base_val[i]
                arr_city = base_val[i+1]
                itinerary_records.append({
                    'day_range': f"Day {day_num}",
                    'place': city_names[dep_city],
                    'type': 0,  # flight record
                    'first_day': day_num
                })
                itinerary_records.append({
                    'day_range': f"Day {day_num}",
                    'place': city_names[arr_city],
                    'type': 0,  # flight record
                    'first_day': day_num
                })
        
        # Step 4: Sort the records: by first_day, then by type (0 for flight, 1 for block), then by place
        itinerary_records_sorted = sorted(itinerary_records, key=lambda x: (x['first_day'], x['type'], x['place']))
        
        # Remove helper keys and create the final itinerary list
        final_itinerary = [{'day_range': rec['day_range'], 'place': rec['place']} for rec in itinerary_records_sorted]
        
        # Output as JSON
        result = {'itinerary': final_itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()