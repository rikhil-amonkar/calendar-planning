import z3

def main():
    # City names and their durations
    cities = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
    durations = [2, 3, 3, 4, 5, 5, 2]
    city_to_duration = dict(zip(cities, durations))
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Adjacency list for direct flights
    adj_list = {
        "Porto": ["Geneva", "Manchester", "Hamburg", "Frankfurt"],
        "Geneva": ["Porto", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"],
        "Mykonos": ["Geneva", "Naples"],
        "Manchester": ["Porto", "Geneva", "Hamburg", "Naples", "Frankfurt"],
        "Hamburg": ["Porto", "Geneva", "Manchester", "Frankfurt"],
        "Naples": ["Geneva", "Mykonos", "Manchester", "Frankfurt"],
        "Frankfurt": ["Porto", "Geneva", "Manchester", "Hamburg", "Naples"]
    }
    
    # Convert adjacency list to indices
    adj_list_index = {}
    for city, neighbors in adj_list.items():
        idx = city_to_index[city]
        adj_list_index[idx] = [city_to_index[n] for n in neighbors]
    
    # Allowed flight pairs
    allowed_pairs = set()
    for a, neighbors in adj_list_index.items():
        for b in neighbors:
            allowed_pairs.add((a, b))
    
    # Z3 variables
    seq = [z3.Int(f'seq_{i}') for i in range(7)]
    cumulative = [z3.Int(f'cum_{i}') for i in range(8)]
    start = [z3.Int(f'start_{i}') for i in range(7)]
    end = [z3.Int(f'end_{i}') for i in range(7)]
    
    s = z3.Solver()
    
    # Constraints for sequence: distinct and within [0,6]
    for i in range(7):
        s.add(seq[i] >= 0)
        s.add(seq[i] < 7)
    s.add(z3.Distinct(seq))
    
    # Helper function to get duration from city index
    def get_dur(idx):
        return z3.If(idx == 0, durations[0],
                z3.If(idx == 1, durations[1],
                z3.If(idx == 2, durations[2],
                z3.If(idx == 3, durations[3],
                z3.If(idx == 4, durations[4],
                z3.If(idx == 5, durations[5],
                z3.If(idx == 6, durations[6], 0)))))))
    
    # Cumulative sum constraints
    s.add(cumulative[0] == 0)
    for i in range(1, 8):
        s.add(cumulative[i] == cumulative[i-1] + get_dur(seq[i-1]))
    
    # Start and end day constraints
    for j in range(7):
        s.add(start[j] == 1 + cumulative[j] - j)
        s.add(end[j] == start[j] + get_dur(seq[j]) - 1)
    
    # Event constraints
    mykonos_index = city_to_index["Mykonos"]
    manchester_index = city_to_index["Manchester"]
    frankfurt_index = city_to_index["Frankfurt"]
    
    mykonos_constraint = z3.Or([z3.And(seq[j] == mykonos_index, start[j] <= 12, end[j] >= 10) for j in range(7)])
    manchester_constraint = z3.Or([z3.And(seq[j] == manchester_index, end[j] >= 15) for j in range(7)])
    frankfurt_constraint = z3.Or([z3.And(seq[j] == frankfurt_index, start[j] <= 6, end[j] >= 5) for j in range(7)])
    
    s.add(mykonos_constraint)
    s.add(manchester_constraint)
    s.add(frankfurt_constraint)
    
    # Flight connection constraints
    for j in range(6):
        conds = []
        for a, b in allowed_pairs:
            conds.append(z3.And(seq[j] == a, seq[j+1] == b))
        s.add(z3.Or(conds))
    
    # Solve and get model
    if s.check() == z3.sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(7)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(7)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(7)]
        
        # Map indices to city names
        city_sequence = [cities[idx] for idx in seq_val]
        
        # Generate itinerary
        itinerary = []
        for j in range(7):
            city_name = city_sequence[j]
            s_day = start_val[j]
            e_day = end_val[j]
            itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": city_name})
            if j < 6:
                itinerary.append({"day_range": f"Day {e_day}", "place": city_name})
                next_city = city_sequence[j+1]
                itinerary.append({"day_range": f"Day {e_day}", "place": next_city})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()