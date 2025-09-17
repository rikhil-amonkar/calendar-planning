import z3
import json

def main():
    # City mappings
    cities = {
        "Dublin": 0,
        "Krakow": 1,
        "Istanbul": 2,
        "Venice": 3,
        "Naples": 4,
        "Brussels": 5,
        "Mykonos": 6,
        "Frankfurt": 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights (unordered pairs)
    allowed_pairs = [
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 7),
        (1, 2), (1, 5), (1, 7),
        (2, 3), (2, 4), (2, 5), (2, 7),
        (3, 4), (3, 5), (3, 7),
        (4, 5), (4, 6), (4, 7),
        (5, 7)
    ]
    
    # Initialize solver
    solver = z3.Solver()
    
    # Arrays for start city, end city, and travel flag for each day (0-indexed for 21 days)
    start_city = [z3.Int(f"start_city_{i}") for i in range(21)]
    end_city = [z3.Int(f"end_city_{i}") for i in range(21)]
    travel = [z3.Bool(f"travel_{i}") for i in range(21)]
    
    # Constrain cities to be between 0 and 7
    for i in range(21):
        solver.add(z3.And(start_city[i] >= 0, start_city[i] <= 7))
        solver.add(z3.And(end_city[i] >= 0, end_city[i] <= 7))
    
    # For day 0, start_city is free
    # For i>0, start_city[i] = end_city[i-1]
    for i in range(1, 21):
        solver.add(start_city[i] == end_city[i-1])
    
    # Travel constraints
    for i in range(21):
        # If not traveling, end city equals start city
        solver.add(z3.Implies(z3.Not(travel[i]), end_city[i] == start_city[i]))
        # If traveling, end city != start city and must be connected by direct flight
        flight_conditions = []
        for a, b in allowed_pairs:
            flight_conditions.append(z3.And(start_city[i] == a, end_city[i] == b))
            flight_conditions.append(z3.And(start_city[i] == b, end_city[i] == a))
        solver.add(z3.Implies(travel[i], z3.And(end_city[i] != start_city[i], z3.Or(flight_conditions))))
    
    # Total travel days must be 7
    solver.add(z3.Sum([z3.If(travel[i], 1, 0) for i in range(21)]) == 7)
    
    # City count constraints
    city_count = [z3.Int(f"city_count_{c}") for c in range(8)]
    for c in range(8):
        count_expr = z3.Sum([
            z3.If(start_city[i] == c, 1, 0) +
            z3.If(z3.And(travel[i], end_city[i] == c), 1, 0)
            for i in range(21)
        ])
        solver.add(city_count[c] == count_expr)
    
    # Required days per city
    solver.add(city_count[0] == 5)  # Dublin
    solver.add(city_count[1] == 4)  # Krakow
    solver.add(city_count[2] == 3)  # Istanbul
    solver.add(city_count[3] == 3)  # Venice
    solver.add(city_count[4] == 4)  # Naples
    solver.add(city_count[5] == 2)  # Brussels
    solver.add(city_count[6] == 4)  # Mykonos
    solver.add(city_count[7] == 3)  # Frankfurt
    
    # Specific date constraints
    # Dublin show: days 11-15 (indices 10-14) must be in Dublin and no travel
    for i in range(10, 15):
        solver.add(travel[i] == False)
        solver.add(start_city[i] == 0)
    
    # Mykonos relatives: must be in Mykonos on at least one day between day1-4 (indices 0-3)
    mykonos_constraints = []
    for i in range(0, 4):
        mykonos_constraints.append(z3.Or(start_city[i] == 6, z3.And(travel[i], end_city[i] == 6)))
    solver.add(z3.Or(mykonos_constraints))
    
    # Istanbul friend: must be in Istanbul on at least one day between day9-11 (indices 8-10)
    istanbul_constraints = []
    for i in range(8, 11):
        istanbul_constraints.append(z3.Or(start_city[i] == 2, z3.And(travel[i], end_city[i] == 2)))
    solver.add(z3.Or(istanbul_constraints))
    
    # Frankfurt friends: must be in Frankfurt on at least one day between day15-17 (indices 14-16)
    frankfurt_constraints = []
    for i in range(14, 17):
        frankfurt_constraints.append(z3.Or(start_city[i] == 7, z3.And(travel[i], end_city[i] == 7)))
    solver.add(z3.Or(frankfurt_constraints))
    
    # Check for a solution
    if solver.check() == z3.sat:
        model = solver.model()
        end_city_values = [model.eval(end_city[i]).as_long() for i in range(21)]
        
        # Group consecutive days with the same end city
 itinerary = []
        current_city = end_city_values[0]
        start_day = 1
        for day_idx in range(1, 21):
            if end_city_values[day_idx] != current_city:
                end_day = day_idx
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": city_names[current_city]
                })
                current_city = end_city_values[day_idx]
                start_day = day_idx + 1
        itinerary.append({
            "day_range": f"Day {start_day}-21",
            "place": city_names[current_city]
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()