from z3 import *
import json

def main():
    # City names and their indices
    city_names = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    city_index = {name: idx for idx, name in enumerate(city_names)}
    
    # Required days for each city (index: 0 to 8)
    req_days_array = [3, 5, 2, 5, 5, 4, 2, 2, 4]
    dur_array = [d - 1 for d in req_days_array]  # Duration = end - start, so end = start + (days - 1)
    
    # Direct flight pairs (both directions)
    flight_pairs = [
        ('Venice', 'Nice'), ('Naples', 'Amsterdam'), ('Barcelona', 'Nice'), ('Amsterdam', 'Nice'),
        ('Stuttgart', 'Valencia'), ('Stuttgart', 'Porto'), ('Split', 'Stuttgart'), ('Split', 'Naples'),
        ('Valencia', 'Amsterdam'), ('Barcelona', 'Porto'), ('Valencia', 'Naples'), ('Venice', 'Amsterdam'),
        ('Barcelona', 'Naples'), ('Barcelona', 'Valencia'), ('Split', 'Amsterdam'), ('Barcelona', 'Venice'),
        ('Stuttgart', 'Amsterdam'), ('Naples', 'Nice'), ('Venice', 'Stuttgart'), ('Split', 'Barcelona'),
        ('Porto', 'Nice'), ('Barcelona', 'Stuttgart'), ('Venice', 'Naples'), ('Porto', 'Amsterdam'),
        ('Porto', 'Valencia'), ('Stuttgart', 'Naples'), ('Barcelona', 'Amsterdam')
    ]
    
    allowed_edges_set = set()
    for a, b in flight_pairs:
        a_idx = city_index[a]
        b_idx = city_index[b]
        allowed_edges_set.add((a_idx, b_idx))
        allowed_edges_set.add((b_idx, a_idx))
    
    # Create the solver
    s = Solver()
    
    # i: position index of Barcelona (0..8), but we know it must be between 1 and 6 (since Barcelona must be followed by Venice and not last)
    i = Int('i')
    s.add(i >= 1, i <= 6)
    
    # p: permutation of cities (positions 0 to 8)
    p = [Int('p_%d' % j) for j in range(9)]
    # Each p[j] is between 0 and 8
    for j in range(9):
        s.add(p[j] >= 0, p[j] <= 8)
    # Distinct permutation
    s.add(Distinct(p))
    # Barcelona (index 7) is at position i, Venice (index 4) is at position i+1
    s.add(p[i] == 7)
    s.add(p[i+1] == 4)
    
    # start_pos and end_pos for each position in the sequence
    start_pos = [Int('start_pos_%d' % j) for j in range(9)]
    end_pos = [Int('end_pos_%d' % j) for j in range(9)]
    
    # Start at day 1 and end at day 24
    s.add(start_pos[0] == 1)
    s.add(end_pos[8] == 24)
    
    # Consecutive cities: end_pos[j] = start_pos[j+1]
    for j in range(8):
        s.add(end_pos[j] == start_pos[j+1])
    
    # For each position j, end_pos[j] = start_pos[j] + (duration of the city at p[j])
    for j in range(9):
        dur_expr = If(
            p[j] == 0, dur_array[0],
            If(p[j] == 1, dur_array[1],
            If(p[j] == 2, dur_array[2],
            If(p[j] == 3, dur_array[3],
            If(p[j] == 4, dur_array[4],
            If(p[j] == 5, dur_array[5],
            If(p[j] == 6, dur_array[6],
            If(p[j] == 7, dur_array[7],
            If(p[j] == 8, dur_array[8], 0)
            ))))))))
        s.add(end_pos[j] == start_pos[j] + dur_expr)
    
    # Barcelona must start at day 5 (due to workshop on day 5 and 6)
    s.add(start_pos[i] == 5)
    
    # Previous city to Barcelona (at position i-1) must have: start_pos[i-1] = 6 - req_days[ p[i-1] ]
    prev_city = p[i-1]
    req_prev_expr = If(
        prev_city == 0, req_days_array[0],
        If(prev_city == 1, req_days_array[1],
        If(prev_city == 2, req_days_array[2],
        If(prev_city == 3, req_days_array[3],
        If(prev_city == 5, req_days_array[5],
        If(prev_city == 6, req_days_array[6],
        If(prev_city == 8, req_days_array[8], 0)
        ))))))
    s.add(start_pos[i-1] == 6 - req_prev_expr)
    
    # Flight edges: for each consecutive pair, (p[j], p[j+1]) must be in allowed_edges_set
    for j in range(8):
        edge_conds = []
        for (a, b) in allowed_edges_set:
            edge_conds.append(And(p[j] == a, p[j+1] == b))
        s.add(Or(edge_conds))
    
    # Naples (index 0): must be between day 18 and 20 at least one day -> stay must overlap [18,20]: start_pos <= 20 and end_pos >= 18
    for j in range(9):
        cond_naples = If(
            p[j] == 0,
            And(start_pos[j] <= 20, start_pos[j] + 2 >= 18),  # end_pos = start_pos + 2 (since 3 days: start, start+1, start+2)
            True
        )
        s.add(cond_naples)
    
    # Nice (index 6): must be between day 23 and 24 at least one day: so start_pos <= 24 and end_pos >= 23 -> and since duration=2: end_pos = start_pos+1
    for j in range(9):
        cond_nice = If(
            p[j] == 6,
            And(start_pos[j] <= 24, start_pos[j] + 1 >= 23),
            True
        )
        s.add(cond_nice)
    
    # Check the model
    if s.check() == sat:
        m = s.model()
        i_val = m[i].as_long()
        p_vals = [m[p_j].as_long() for p_j in p]
        start_vals = [m[sp].as_long() for sp in start_pos]
        end_vals = [m[ep].as_long() for ep in end_pos]
        
        # Build itinerary
        itinerary = []
        for j in range(9):
            s_val = start_vals[j]
            e_val = end_vals[j]
            city_idx = p_vals[j]
            city_name = city_names[city_idx]
            
            # Record for the entire stay
            if s_val == e_val:
                range_str = "Day %d" % s_val
            else:
                range_str = "Day %d-%d" % (s_val, e_val)
            itinerary.append({"day_range": range_str, "place": city_name})
            
            # If not the last city, add flight day records
            if j < 8:
                # Departure from current city on day e_val
                itinerary.append({"day_range": "Day %d" % e_val, "place": city_name})
                # Arrival in next city on day e_val
                next_city_idx = p_vals[j+1]
                next_city_name = city_names[next_city_idx]
                itinerary.append({"day_range": "Day %d" % e_val, "place": next_city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()