from z3 import *

def main():
    # City indices: 0=Reykjavik, 1=Istanbul, 2=Edinburgh, 3=Oslo, 4=Stuttgart, 5=Bucharest
    city_names = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
    durations = [5, 4, 5, 2, 3, 5]
    
    # Direct flight edges (undirected)
    edges = [(0, 3), (0, 4),
             (1, 2), (1, 3), (1, 4), (1, 5),
             (2, 3), (2, 4),
             (3, 5)]
    
    # Create solver
    s = Solver()
    
    # Order variables: o0, o1, ... o5: the city index at each position
    order_vars = [Int('o%d' % i) for i in range(6)]
    # Start and end days for each segment (in the order of the itinerary)
    start_seg = [Int('start_seg%d' % i) for i in range(6)]
    end_seg = [Int('end_seg%d' % i) for i in range(6)]
    
    # Each order_vars is between 0 and 5
    for i in range(6):
        s.add(order_vars[i] >= 0, order_vars[i] <= 5)
    # All order_vars are distinct
    s.add(Distinct(order_vars))
    
    # Start of the first segment is 1
    s.add(start_seg[0] == 1)
    # End of the last segment is 19
    s.add(end_seg[5] == 19)
    
    # Function to get duration of a city by its index
    def city_duration(city_var):
        return If(city_var == 0, durations[0],
               If(city_var == 1, durations[1],
               If(city_var == 2, durations[2],
               If(city_var == 3, durations[3],
               If(city_var == 4, durations[4],
               If(city_var == 5, durations[5], 0))))))
    
    # Constraints for each segment
    for i in range(6):
        dur = city_duration(order_vars[i])
        s.add(end_seg[i] == start_seg[i] + dur - 1)
    
    # Constraints for consecutive segments: the end of segment i is the start of segment i+1
    for i in range(5):
        s.add(start_seg[i+1] == end_seg[i])
    
    # Event constraints: 
    # For Istanbul (city1) and Oslo (city3), we need to extract their start and end days
    ist_start, ist_end = Int('ist_start'), Int('ist_end')
    osl_start, osl_end = Int('osl_start'), Int('osl_end')
    
    ist_start_expr = start_seg[0]
    ist_end_expr = end_seg[0]
    osl_start_expr = start_seg[0]
    osl_end_expr = end_seg[0]
    
    for i in range(6):
        ist_start_expr = If(order_vars[i] == 1, start_seg[i], ist_start_expr)
        ist_end_expr = If(order_vars[i] == 1, end_seg[i], ist_end_expr)
        osl_start_expr = If(order_vars[i] == 3, start_seg[i], osl_start_expr)
        osl_end_expr = If(order_vars[i] == 3, end_seg[i], osl_end_expr)
    
    s.add(ist_start_expr <= 5, ist_end_expr >= 8)
    s.add(osl_start_expr <= 8, osl_end_expr >= 9)
    
    # Constraint: Istanbul must be immediately followed by Oslo
    consecutive_ist_osl = Or([And(order_vars[i] == 1, order_vars[i+1] == 3) for i in range(5)])
    s.add(consecutive_ist_osl)
    
    # Flight constraints: consecutive cities must be connected by a direct flight
    for i in range(5):
        a = order_vars[i]
        b = order_vars[i+1]
        conds = []
        for (x, y) in edges:
            conds.append(And(a == x, b == y))
            conds.append(And(a == y, b == x))
        s.add(Or(conds))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        order_sol = [m.evaluate(order_vars[i]).as_long() for i in range(6)]
        start_sol = [m.evaluate(start_seg[i]).as_long() for i in range(6)]
        end_sol = [m.evaluate(end_seg[i]).as_long() for i in range(6)]
        
        itinerary = []
        for i in range(6):
            city_idx = order_sol[i]
            city_name = city_names[city_idx]
            s_val = start_sol[i]
            e_val = end_sol[i]
            # Entire stay for the city
            itinerary.append({"day_range": f"Day {s_val}-{e_val}", "place": city_name})
            if i < 5:
                next_city_idx = order_sol[i+1]
                next_city_name = city_names[next_city_idx]
                # Departure from current city on the flight day
                itinerary.append({"day_range": f"Day {e_val}", "place": city_name})
                # Arrival at next city on the flight day
                itinerary.append({"day_range": f"Day {e_val}", "place": next_city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()