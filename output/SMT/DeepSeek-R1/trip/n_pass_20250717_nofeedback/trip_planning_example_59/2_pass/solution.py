import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Create a 16x3 grid of boolean variables: days 0 to 15, cities: 0=Bucharest, 1=Lyon, 2=Porto
    b = [[z3.Bool(f"day{i}_city{j}") for j in range(3)] for i in range(16)]
    
    # Constraint: first day only Bucharest
    solver.add(b[0][0] == True)   # in Bucharest
    solver.add(b[0][1] == False)  # not in Lyon
    solver.add(b[0][2] == False)  # not in Porto
    
    # For each day, add constraints: at least one city, at most two, and only valid combinations
    for i in range(16):
        # At least one city
        solver.add(z3.Or(b[i][0], b[i][1], b[i][2]))
        
        # Not all three at the same time
        solver.add(z3.Not(z3.And(b[i][0], b[i][1], b[i][2])))
        
        # If both Bucharest and Porto are present, then Lyon must be present (but then we have all three, which is forbidden by the above)
        # So we add: not (Bucharest and Porto) without Lyon -> but the above already prevents all three, so this is redundant?
        # Instead, we explicitly prevent Bucharest and Porto together without Lyon? But if they are together, then Lyon must be present -> then all three, which is forbidden.
        # So we don't need an extra constraint.
    
    # Total days in each city
    total_b = z3.Sum([z3.If(b[i][0], 1, 0) for i in range(16)])
    total_l = z3.Sum([z3.If(b[i][1], 1, 0) for i in range(16)])
    total_p = z3.Sum([z3.If(b[i][2], 1, 0) for i in range(16)])
    solver.add(total_b == 7, total_l == 7, total_p == 4)
    
    # Wedding constraint: at least one day in the first 7 days (days 1 to 7, indices 0 to 6) in Bucharest
    solver.add(z3.Or([b[i][0] for i in range(7)]))
    
    # Connectivity: consecutive days share at least one city
    for i in range(15):
        solver.add(z3.Or(
            z3.And(b[i][0], b[i+1][0]),
            z3.And(b[i][1], b[i+1][1]),
            z3.And(b[i][2], b[i+1][2])
        ))
    
    # Check and get the model
    if solver.check() == z3.sat:
        model = solver.model()
        # Create a list of sets for each day
        city_names = ["Bucharest", "Lyon", "Porto"]
        days = []
        for i in range(16):
            s = set()
            for j in range(3):
                if z3.is_true(model.evaluate(b[i][j])):
                    s.add(city_names[j])
            days.append(s)
        
        # Group consecutive days with the same set of cities
        itinerary_ranges = []
        start_index = 0
        current_set = days[0]
        for i in range(1, 16):
            if days[i] == current_set:
                continue
            else:
                start_day = start_index + 1
                end_day = i  # i is the first index of the next group, so the last of this group is i-1 -> day number = i
                if start_index == i-1:
                    day_range_str = f"Day {start_day}"
                else:
                    day_range_str = f"Day {start_day}-{end_day}"
                # Format the place string
                lst = sorted(list(current_set))  # sort to have consistent order
                if len(lst) == 1:
                    place_str = lst[0]
                else:
                    place_str = " and ".join(lst)
                itinerary_ranges.append({"day_range": day_range_str, "place": place_str})
                start_index = i
                current_set = days[i]
        
        # Last group
        start_day = start_index + 1
        end_day = 16
        if start_index == 15:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
        lst = sorted(list(current_set))
        if len(lst) == 1:
            place_str = lst[0]
        else:
            place_str = " and ".join(lst)
        itinerary_ranges.append({"day_range": day_range_str, "place": place_str})
        
        # Output as JSON
        result = {'itinerary': itinerary_ranges}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()