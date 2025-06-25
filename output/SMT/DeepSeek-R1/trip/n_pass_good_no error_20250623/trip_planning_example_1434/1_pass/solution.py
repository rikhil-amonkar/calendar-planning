from z3 import *
import json

def main():
    # City names and their durations
    city_names = ["Rome", "Mykonos", "Lisbon", "Frankfurt", "Nice", "Stuttgart", "Venice", "Dublin", "Bucharest", "Seville"]
    durations = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]
    
    # Flight connections
    flight_pairs_str = "Rome and Stuttgart, Venice and Rome, Dublin and Bucharest, Mykonos and Rome, Seville and Lisbon, Frankfurt and Venice, Venice and Stuttgart, Bucharest and Lisbon, Nice and Mykonos, Venice and Lisbon, Dublin and Lisbon, Venice and Nice, Rome and Seville, Frankfurt and Rome, Nice and Dublin, Rome and Bucharest, Frankfurt and Dublin, Rome and Dublin, Venice and Dublin, Rome and Lisbon, Frankfurt and Lisbon, Nice and Rome, Frankfurt and Nice, Frankfurt and Stuttgart, Frankfurt and Bucharest, Lisbon and Stuttgart, Nice and Lisbon, Seville and Dublin"
    flight_pairs = [pair.split(' and ') for pair in flight_pairs_str.split(', ')]
    
    # Create a set of directed flight edges (both directions)
    flight_edges = set()
    for a, b in flight_pairs:
        i = city_names.index(a)
        j = city_names.index(b)
        flight_edges.add((i, j))
        flight_edges.add((j, i))
    flight_edges = list(flight_edges)
    
    # Create Z3 variables
    s = [Int(f's_{i}') for i in range(10)]  # Sequence of cities (by index)
    pos = [Int(f'pos_{i}') for i in range(10)]  # Position of each city in the sequence
    start_vars = [Int(f'start_{i}') for i in range(10)]  # Start day for each city
    
    solver = Solver()
    
    # Constraints for s: permutation of 0 to 9
    solver.add([And(s_i >= 0, s_i < 10) for s_i in s])
    solver.add(Distinct(s))
    
    # Constraints for pos: pos[i] is the position of city i in s
    for i in range(10):
        or_conditions = []
        for k in range(10):
            or_conditions.append(And(s[k] == i, pos[i] == k))
        solver.add(Or(or_conditions))
    
    # Constraints for start_vars: start_vars[i] = 1 + sum of (durations[j]-1) for all j before i
    for i in range(10):
        sum_before = 0
        for j in range(10):
            if j == i:
                continue
            condition = And(j != i, pos[j] < pos[i])
            sum_before += If(condition, durations[j] - 1, 0)
        solver.add(start_vars[i] == 1 + sum_before)
    
    # Specific constraints
    solver.add(start_vars[city_names.index("Seville")] == 13)  # Seville start day is 13
    mykonos_idx = city_names.index("Mykonos")
    solver.add(And(start_vars[mykonos_idx] >= 9, start_vars[mykonos_idx] <= 11))  # Mykonos between day 9 and 11
    frankfurt_idx = city_names.index("Frankfurt")
    solver.add(start_vars[frankfurt_idx] <= 5)  # Frankfurt starts by day 5
    
    # Flight constraints for consecutive cities in the sequence
    for k in range(9):
        or_conditions = []
        for edge in flight_edges:
            a, b = edge
            or_conditions.append(And(s[k] == a, s[k+1] == b))
        solver.add(Or(or_conditions))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        # Get the sequence
        seq_cities = []
        for i in range(10):
            seq_cities.append(model.eval(s[i]).as_long())
        # Get start days for each city
        start_days = []
        for i in range(10):
            start_days.append(model.eval(start_vars[i]).as_long())
        
        # Build itinerary
        itinerary = []
        for idx, city_idx in enumerate(seq_cities):
            start = start_days[city_idx]
            duration_val = durations[city_idx]
            end = start + duration_val - 1
            place = city_names[city_idx]
            
            # Entire stay record
            itinerary.append({"day_range": f"Day {start}-{end}", "place": place})
            
            # If not last city, add departure record
            if idx < 9:
                itinerary.append({"day_range": f"Day {end}", "place": place})
            
            # If not first city, add arrival record for current city (already handled in previous departure)
            # For the next city, we add its arrival record when processing it
            if idx > 0:
                # But note: we already added the entire stay and departure for the previous city
                # Now, for the current city (starting from idx=1), we need to add the arrival record at the beginning?
                # Instead, we adjust: we added the entire stay and then departure for the previous.
                # Then we add the arrival for the current city at the start of processing the current?
                # But in our loop, we are processing one city at a time.
                # We have already added the arrival record for the current city in the previous iteration? 
                # Actually, no: we add the arrival record when we process the current city.
                # How? We don't have a separate step for arrival. 
                # So we add the arrival record for the current city here, but before the entire stay?
                # But we already added the entire stay and departure for the current city above.
                # Therefore, we need to insert the arrival record for the current city before the entire stay.
                # But we cannot do that in the current loop structure.
                # Instead, we restructure the loop to add the arrival record for the current city (except the first) at the beginning of processing.
                # We do this by moving the arrival record addition to before the entire stay for cities that are not the first.
                pass
        
        # We rebuild the itinerary correctly
        itinerary = []
        # First city
        city_idx0 = seq_cities[0]
        start0 = start_days[city_idx0]
        end0 = start0 + durations[city_idx0] - 1
        itinerary.append({"day_range": f"Day {start0}-{end0}", "place": city_names[city_idx0]})
        if len(seq_cities) > 1:
            itinerary.append({"day_range": f"Day {end0}", "place": city_names[city_idx0]})
        
        # Middle cities (from index1 to index8)
        for idx in range(1, 9):
            city_idx = seq_cities[idx]
            start = start_days[city_idx]
            end = start + durations[city_idx] - 1
            itinerary.append({"day_range": f"Day {start}", "place": city_names[city_idx]})
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_names[city_idx]})
            itinerary.append({"day_range": f"Day {end}", "place": city_names[city_idx]})
        
        # Last city (index9)
        if len(seq_cities) > 1:
            city_idx9 = seq_cities[9]
            start9 = start_days[city_idx9]
            end9 = start9 + durations[city_idx9] - 1
            itinerary.append({"day_range": f"Day {start9}", "place": city_names[city_idx9]})
            itinerary.append({"day_range": f"Day {start9}-{end9}", "place": city_names[city_idx9]})
        
        # Create the final JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()