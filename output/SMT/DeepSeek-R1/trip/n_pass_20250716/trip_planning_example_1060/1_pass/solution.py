from z3 import *

def main():
    # City indices: 0:Reykjavik, 1:Stuttgart, 2:Valencia, 3:Geneva, 4:Vilnius, 5:Seville, 6:Munich, 7:Istanbul
    city_names = {
        0: "Reykjavik",
        1: "Stuttgart",
        2: "Valencia",
        3: "Geneva",
        4: "Vilnius",
        5: "Seville",
        6: "Munich",
        7: "Istanbul"
    }
    
    durations = {
        0: 4,  # Reykjavik
        1: 4,  # Stuttgart
        2: 5,  # Valencia
        3: 5,  # Geneva
        4: 4,  # Vilnius
        5: 3,  # Seville
        6: 3,  # Munich
        7: 4   # Istanbul
    }
    
    directed_flights = [
        (0, 6), (6, 0),  # Reykjavik <-> Munich
        (0, 1),           # Reykjavik -> Stuttgart
        (1, 2), (2, 1),   # Stuttgart <-> Valencia
        (1, 7), (7, 1),   # Stuttgart <-> Istanbul
        (3, 7), (7, 3),   # Geneva <-> Istanbul
        (6, 3), (3, 6),   # Munich <-> Geneva
        (7, 4), (4, 7),   # Istanbul <-> Vilnius
        (2, 5), (5, 2),   # Valencia <-> Seville
        (2, 7), (7, 2),   # Valencia <-> Istanbul
        (4, 6),           # Vilnius -> Munich
        (5, 6), (6, 5),   # Seville <-> Munich
        (6, 7), (7, 6),   # Munich <-> Istanbul
        (2, 3), (3, 2),   # Valencia <-> Geneva
        (2, 6), (6, 2)    # Valencia <-> Munich
    ]
    
    s = Solver()
    
    # Order variables for the 8 cities: first two are fixed, the next six are variables
    order = [0, 1]  # Reykjavik, Stuttgart
    order_vars = [Int('o2'), Int('o3'), Int('o4'), Int('o5'), Int('o6'), Int('o7')]
    order.extend(order_vars)
    
    # s[i] and e[i] for each position i in the itinerary
    starts = [Int(f's_{i}') for i in range(8)]
    ends = [Int(f'e_{i}') for i in range(8)]
    
    # Duration array: mapping from city index to its duration
    duration_arr = Array('durations', IntSort(), IntSort())
    for idx, dur in durations.items():
        duration_arr = Store(duration_arr, idx, dur)
    
    # Constraints for the order: last six must be distinct and in [2,7]
    s.add(Distinct(order_vars))
    for i in range(2, 8):
        s.add(And(order[i] >= 2, order[i] <= 7))
    
    # Constraints for start and end days
    s.add(starts[0] == 1)
    s.add(ends[0] == starts[0] + (duration_arr[order[0]] - 1))
    
    for i in range(1, 8):
        s.add(starts[i] == ends[i-1])
        s.add(ends[i] == starts[i] + (duration_arr[order[i]] - 1))
    
    # Fixed start days for Munich and Istanbul
    for i in range(8):
        s.add(If(order[i] == 6, starts[i] == 13, True))
        s.add(If(order[i] == 7, starts[i] == 19, True))
    
    # The entire trip must end at day 25
    s.add(ends[7] == 25)
    
    # Flight constraints between consecutive cities
    for i in range(7):
        options = []
        for (a, b) in directed_flights:
            options.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(options))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        resolved_order = []
        resolved_starts = []
        resolved_ends = []
        
        for i in range(8):
            if i < 2:
                # Fixed
                city_index = order[i]
            else:
                # Variable
                city_index = model[order[i]].as_long()
            resolved_order.append(city_index)
            
            start_val = model[starts[i]].as_long()
            end_val = model[ends[i]].as_long()
            resolved_starts.append(start_val)
            resolved_ends.append(end_val)
        
        # Build the itinerary list
        itinerary = []
        for i in range(8):
            city_idx = resolved_order[i]
            place = city_names[city_idx]
            start = resolved_starts[i]
            end = resolved_ends[i]
            
            # The entire consecutive stay
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": place})
            
            # If not the first city, add a record for the start day (travel day of arrival)
            if i > 0:
                itinerary.append({"day_range": f"Day {start}", "place": place})
            
            # If not the last city, add a record for the end day (travel day of departure)
            if i < 7:
                itinerary.append({"day_range": f"Day {end}", "place": place})
        
        # Output the result as JSON
        output_dict = {"itinerary": itinerary}
        print(output_dict)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()