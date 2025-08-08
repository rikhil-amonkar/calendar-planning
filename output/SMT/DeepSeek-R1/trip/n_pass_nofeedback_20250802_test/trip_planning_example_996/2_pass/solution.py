from z3 import *

def main():
    # Define city names and their required days
    city_names = ["Mykonos", "Prague", "Nice", "Valencia", "Riga", "Zurich", "Bucharest"]
    req_days = [3, 3, 2, 5, 5, 5, 5]
    
    # Direct flights as a list of strings
    edges_list = [
        "Mykonos and Nice",
        "Mykonos and Zurich",
        "Prague and Bucharest",
        "Valencia and Bucharest",
        "Zurich and Prague",
        "Riga and Nice",
        "Zurich and Riga",
        "Zurich and Bucharest",
        "Zurich and Valencia",
        "Bucharest and Riga",
        "Prague and Riga",
        "Prague and Valencia",
        "Zurich and Nice"
    ]
    
    # Build allowed flight pairs
    allowed_pairs = set()
    for edge_str in edges_list:
        parts = edge_str.split(" and ")
        if len(parts) != 2:
            continue
        a, b = parts
        try:
            idxA = city_names.index(a)
            idxB = city_names.index(b)
            allowed_pairs.add((idxA, idxB))
            allowed_pairs.add((idxB, idxA))
        except:
            continue  # Skip if city not found (shouldn't happen)
    
    # Create Z3 solver and variables for the order of cities
    s = Solver()
    order = [Int(f'order_{i}') for i in range(7)]
    
    # Each order variable must be between 0 and 6 and all distinct
    s.add([And(order[i] >= 0, order[i] < 7) for i in range(7)])
    s.add(Distinct(order))
    
    # Define start days for each city in the order
    start = [1]  # start[0] = 1
    for i in range(1, 7):
        # Compute required days for the previous city in the order
        req_prev = Sum([If(order[i-1] == j, req_days[j], 0) for j in range(7)])
        # start[i] = start[i-1] + (req_prev - 1)
        start.append(start[i-1] + req_prev - 1)
    
    # Add constraints for Mykonos and Prague event dates
    for i in range(7):
        # Mykonos (index 0) must start by day 3
        s.add(If(order[i] == 0, start[i] <= 3, True))
        # Prague (index 1) must start between days 5 and 9 inclusive
        s.add(If(order[i] == 1, And(start[i] >= 5, start[i] <= 9), True))
    
    # Add constraints for direct flights between consecutive cities
    for i in range(6):
        # Check if (order[i], order[i+1]) is in allowed_pairs
        conds = []
        for (a, b) in allowed_pairs:
            conds.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(conds))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(7)]
        
        # Compute start days from the model
        start_days = [1]
        for i in range(1, 7):
            prev_city = order_vals[i-1]
            start_days.append(start_days[i-1] + req_days[prev_city] - 1)
        
        # Build itinerary
        itinerary = []
        for i in range(7):
            city_idx = order_vals[i]
            city_name = city_names[city_idx]
            s_day = start_days[i]
            e_day = s_day + req_days[city_idx] - 1
            day_range = f"Day {s_day}-{e_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()