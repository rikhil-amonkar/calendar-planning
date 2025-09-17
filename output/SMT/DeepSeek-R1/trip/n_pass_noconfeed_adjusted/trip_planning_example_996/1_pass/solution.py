import z3
import json

def main():
    # City mapping
    cities = {
        0: "Mykonos",
        1: "Nice",
        2: "Zurich",
        3: "Prague",
        4: "Bucharest",
        5: "Valencia",
        6: "Riga"
    }
    
    # Desired days per city (by index)
    desired_days = [3, 2, 5, 3, 5, 5, 5]
    
    # Direct flights (as unordered pairs)
    flights = [
        (0, 1), (0, 2), (3, 4), (5, 4), (2, 3),
        (6, 1), (2, 6), (2, 4), (2, 5), (4, 6),
        (3, 6), (3, 5), (2, 1)
    ]
    flight_set = set(frozenset(pair) for pair in flights)
    
    # Create solver
    solver = z3.Solver()
    
    # Order of cities (7 integers)
    order = [z3.Int(f"order_{i}") for i in range(7)]
    
    # Each city must be between 0 and 6
    for o in order:
        solver.add(z3.And(o >= 0, o <= 6))
    
    # All cities must be distinct
    solver.add(z3.Distinct(order))
    
    # Start and end days for each position
    start_pos = [z3.Int(f"start_{i}") for i in range(7)]
    end_pos = [z3.Int(f"end_{i}") for i in range(7)]
    
    # First city starts on day 1
    solver.add(start_pos[0] == 1)
    
    # Compute start and end days based on desired days
    for i in range(7):
        if i < 6:
            solver.add(start_pos[i+1] == start_pos[i] + desired_days[order[i]] - 1)
        solver.add(end_pos[i] == start_pos[i] + desired_days[order[i]] - 1)
    
    # Total days must be 22
    solver.add(end_pos[6] == 22)
    
    # Mykonos (city 0) must be visited between day 1-3
    for i in range(7):
        solver.add(z3.Implies(order[i] == 0, z3.And(start_pos[i] <= 3, end_pos[i] >= 1)))
    
    # Prague (city 3) must be visited between day 7-9
    for i in range(7):
        solver.add(z3.Implies(order[i] == 3, z3.And(start_pos[i] <= 9, end_pos[i] >= 7)))
    
    # Direct flight constraints between consecutive cities
    for i in range(6):
        city_pair = z3.And(
            z3.Or(
                z3.And(order[i] == a, order[i+1] == b),
                z3.And(order[i] == b, order[i+1] == a)
            )
            for a, b in flights
        )
        solver.add(city_pair)
    
    # Check feasibility
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract the order and start days
        order_val = [model.evaluate(o).as_long() for o in order]
        start_val = [model.evaluate(s).as_long() for s in start_pos]
        end_val = [model.evaluate(e).as_long() for e in end_pos]
        
        # Build itinerary
        itinerary = []
        for i in range(7):
            city_index = order_val[i]
            start_day = start_val[i]
            end_day = end_val[i]
            city_name = cities[city_index]
            
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            
            itinerary.append({
                "day_range": day_range,
                "place": city_name
            })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()