from z3 import *

def main():
    # Define city names and their indices
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Reykjavik", "Prague"]
    city_to_idx = {name: idx for idx, name in enumerate(cities)}
    
    # Stay durations and stay_minus (stay - 1)
    stay_arr = [4, 5, 4, 3, 4, 3]  # Helsinki, Valencia, Dubrovnik, Porto, Reykjavik, Prague
    stay_minus_arr = [s-1 for s in stay_arr]  # [3,4,3,2,3,2]
    
    # Adjacency matrix for direct flights (symmetric)
    adj = [
        [0, 0, 1, 0, 1, 1],  # Helsinki (0)
        [0, 0, 0, 1, 0, 1],  # Valencia (1)
        [1, 0, 0, 0, 0, 0],  # Dubrovnik (2)
        [0, 1, 0, 0, 0, 0],  # Porto (3)
        [1, 0, 0, 0, 0, 1],  # Reykjavik (4)
        [1, 1, 0, 0, 1, 0]   # Prague (5)
    ]
    
    # Create a set of allowed edges (undirected)
    allowed_edges = []
    for i in range(6):
        for j in range(6):
            if adj[i][j] == 1:
                allowed_edges.append((i, j))
    
    # Z3 solver setup
    s = Solver()
    
    # Order variables: 6 Ints for the permutation
    order = [Int(f'o{i}') for i in range(6)]
    
    # Constraints: each order[i] in [0,5] and distinct
    for i in range(6):
        s.add(And(order[i] >= 0, order[i] < 6))
    s.add(Distinct(order))
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(5):
        cons = []
        for a, b in allowed_edges:
            cons.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(cons))
    
    # Porto constraint: find porto_index (position of Porto in the order)
    porto_index = Int('porto_index')
    s.add(porto_index >= 0, porto_index < 6)
    porto_cons = []
    for k in range(6):
        porto_cons.append(And(porto_index == k, order[k] == city_to_idx["Porto"]))
    s.add(Or(porto_cons))
    
    # Define stay_minus_arr_z3 as a Z3 array
    stay_minus_arr_z3 = Array('stay_minus', IntSort(), IntSort())
    for idx in range(6):
        s.add(stay_minus_arr_z3[idx] == stay_minus_arr[idx])
    
    # Prefix_sum: sum of stay_minus for cities before Porto
    prefix_sum = 0
    for i in range(6):
        prefix_sum = prefix_sum + If(i < porto_index, stay_minus_arr_z3[order[i]], 0)
    s.add(prefix_sum >= 13, prefix_sum <= 15)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(6)]
        porto_index_val = m.evaluate(porto_index).as_long()
        
        # Compute start days for each city
        start_days = [1]  # start day of first city is 1
        for i in range(1, 6):
            prev_city_idx = order_vals[i-1]
            prev_stay_minus = stay_minus_arr[prev_city_idx]
            start_days.append(start_days[i-1] + prev_stay_minus)
        
        # End days: start[i] + stay_minus_arr[order_vals[i]]
        end_days = []
        for i in range(6):
            city_idx = order_vals[i]
            end_days.append(start_days[i] + stay_minus_arr[city_idx])
        
        # Build itinerary
        itinerary = []
        for i in range(6):
            city_name = cities[order_vals[i]]
            s_day = start_days[i]
            e_day = end_days[i]
            
            # Entire block for the city
            if s_day == e_day:
                day_range_str = f"Day {s_day}"
            else:
                day_range_str = f"Day {s_day}-{e_day}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last city, add travel records
            if i < 5:
                # Departure from current city
                itinerary.append({"day_range": f"Day {e_day}", "place": city_name})
                # Arrival at next city
                next_city_name = cities[order_vals[i+1]]
                itinerary.append({"day_range": f"Day {e_day}", "place": next_city_name})
        
        # Output as JSON-like dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()