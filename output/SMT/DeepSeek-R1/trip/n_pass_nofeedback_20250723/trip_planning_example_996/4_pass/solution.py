from z3 import *

def main():
    # Define city names and their required stay days
    city_names = ["Mykonos", "Prague", "Nice", "Valencia", "Riga", "Zurich", "Bucharest"]
    req_days = [3, 3, 2, 5, 5, 5, 5]
    n = len(city_names)
    
    # Direct flights as integer indices
    allowed_indices = set()
    flight_pairs = [
        ("Mykonos", "Nice"), ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"), ("Valencia", "Bucharest"),
        ("Zurich", "Prague"), ("Riga", "Nice"),
        ("Zurich", "Riga"), ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"), ("Bucharest", "Riga"),
        ("Prague", "Riga"), ("Prague", "Valencia"),
        ("Zurich", "Nice")
    ]
    for city1, city2 in flight_pairs:
        i = city_names.index(city1)
        j = city_names.index(city2)
        allowed_indices.add((i, j))
        allowed_indices.add((j, i))
    
    # Create Z3 solver and variables
    s = Solver()
    order = [Int(f'order_{i}') for i in range(n)]
    
    # Each order must be between 0 and n-1 and all distinct
    s.add([And(order[i] >= 0, order[i] < n) for i in range(n)])
    s.add(Distinct(order))
    
    # Create array for required days
    req_days_arr = Array('req_days', IntSort(), IntSort())
    for i in range(n):
        s.add(req_days_arr[i] == req_days[i])
    
    # Create start day variables
    start = [Int(f'start_{i}') for i in range(n)]
    s.add(start[0] == 1)  # First city starts on day 1
    
    # Add travel days and stay durations
    for i in range(1, n):
        s.add(start[i] == start[i-1] + Select(req_days_arr, order[i-1]) + 1)
    
    # Create end day variables
    end = [Int(f'end_{i}') for i in range(n)]
    for i in range(n):
        s.add(end[i] == start[i] + Select(req_days_arr, order[i]) - 1)
    
    # Total trip within 22 days
    s.add(end[n-1] <= 22)
    
    # Event constraints
    for i in range(n):
        city_idx = order[i]
        # Mykonos must start by day 3
        s.add(Implies(city_idx == 0, And(start[i] >= 1, start[i] <= 3)))
        # Prague must start between days 5-9
        s.add(Implies(city_idx == 1, And(start[i] >= 5, start[i] <= 9)))
    
    # Flight constraints between consecutive cities
    for i in range(n-1):
        city1 = order[i]
        city2 = order[i+1]
        conds = []
        for pair in allowed_indices:
            conds.append(And(city1 == pair[0], city2 == pair[1]))
        s.add(Or(conds))
    
    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(n)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(n)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_idx = order_vals[i]
            city_name = city_names[city_idx]
            s_day = start_vals[i]
            e_day = end_vals[i]
            day_range = f"Day {s_day}-{e_day}" if s_day != e_day else f"Day {s_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        result = {"itinerary": itinerary}
        print("Plan found:", result)
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()