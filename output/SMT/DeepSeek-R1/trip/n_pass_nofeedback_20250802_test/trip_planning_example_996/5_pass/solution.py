from z3 import *

def main():
    city_names = ["Mykonos", "Prague", "Nice", "Valencia", "Riga", "Zurich", "Bucharest"]
    req_days = [3, 3, 2, 5, 5, 5, 5]
    n_cities = len(city_names)
    n_positions = n_cities
    
    # Build allowed flight connections
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
        try:
            idx1 = city_names.index(city1)
            idx2 = city_names.index(city2)
            allowed_indices.add((idx1, idx2))
            allowed_indices.add((idx2, idx1))
        except:
            continue
    
    s = Solver()
    
    # Active positions and city assignments
    active = [Bool(f'active_{i}') for i in range(n_positions)]
    city = [Int(f'city_{i}') for i in range(n_positions)]
    
    # First position must be active
    s.add(active[0] == True)
    
    # Active positions are contiguous
    for i in range(1, n_positions):
        s.add(Implies(active[i], active[i-1]))
    
    # City assignments for active positions
    for i in range(n_positions):
        s.add(If(active[i], And(city[i] >= 0, city[i] < n_cities), True))
    
    # Mykonos (0) and Prague (1) must be included
    s.add(Or([And(active[i], city[i] == 0) for i in range(n_positions)]))
    s.add(Or([And(active[i], city[i] == 1) for i in range(n_positions)]))
    
    # Cities appear at most once
    for c in range(n_cities):
        s.add(AtMost(*[And(active[i], city[i] == c) for i in range(n_positions)], 1))
    
    # Start and end days
    start = [Int(f'start_{i}') for i in range(n_positions)]
    end = [Int(f'end_{i}') for i in range(n_positions)]
    
    # First active position starts on day 1
    s.add(If(active[0], start[0] == 1, True))
    
    # Subsequent positions account for travel days
    for i in range(1, n_positions):
        s.add(If(active[i], start[i] == end[i-1] + 2, True))
    
    # End day calculation
    for i in range(n_positions):
        for c in range(n_cities):
            s.add(If(And(active[i], city[i] == c), end[i] == start[i] + req_days[c] - 1, True))
    
    # Event constraints
    for i in range(n_positions):
        s.add(If(And(active[i], city[i] == 0), And(start[i] >= 1, start[i] <= 3), True))
        s.add(If(And(active[i], city[i] == 1), And(start[i] >= 5, start[i] <= 9), True))
    
    # Flight connections
    for i in range(n_positions - 1):
        cond = And(active[i], active[i+1])
        flight_cond = Or([And(city[i] == a, city[i+1] == b) for (a, b) in allowed_indices])
        s.add(Implies(cond, flight_cond))
    
    # Total trip duration <= 22 days
    last_end = end[0]
    for i in range(1, n_positions):
        last_end = If(active[i], end[i], last_end)
    s.add(last_end <= 22)
    
    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        active_vals = [m.evaluate(active[i]) for i in range(n_positions)]
        city_vals = [m.evaluate(city[i]) for i in range(n_positions)]
        start_vals = [m.evaluate(start[i]) for i in range(n_positions)]
        end_vals = [m.evaluate(end[i]) for i in range(n_positions)]
        
        itinerary = []
        for i in range(n_positions):
            if is_true(active_vals[i]):
                c = city_vals[i].as_long()
                s_day = start_vals[i].as_long()
                e_day = end_vals[i].as_long()
                day_range = f"Day {s_day}-{e_day}"
                itinerary.append({"day_range": day_range, "place": city_names[c]})
        
        print("Plan found:", {"itinerary": itinerary})
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()