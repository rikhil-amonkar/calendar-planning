import z3
import json

def main():
    solver = z3.Solver()
    
    # Create boolean variables for each day (0-15) and city (0=Bucharest, 1=Lyon, 2=Porto)
    presence = [[z3.Bool(f"d{i}_c{j}") for j in range(3)] for i in range(16)]
    
    # Day 1 must be Bucharest only
    solver.add(presence[0][0] == True)
    solver.add(presence[0][1] == False)
    solver.add(presence[0][2] == False)
    
    # Daily constraints
    for i in range(16):
        # Must be in at least one city
        solver.add(z3.Or(presence[i][0], presence[i][1], presence[i][2]))
        
        # Cannot be in all three cities
        solver.add(z3.Not(z3.And(presence[i][0], presence[i][1], presence[i][2])))
        
        # Can only be in two cities if they're adjacent
        solver.add(z3.Implies(
            z3.And(presence[i][0], presence[i][2]),  # Bucharest and Porto together
            False
        ))
    
    # Total days per city
    total_bucharest = z3.Sum([z3.If(presence[i][0], 1, 0) for i in range(16)])
    total_lyon = z3.Sum([z3.If(presence[i][1], 1, 0) for i in range(16)])
    total_porto = z3.Sum([z3.If(presence[i][2], 1, 0) for i in range(16)])
    solver.add(total_bucharest == 7, total_lyon == 7, total_porto == 4)
    
    # Wedding constraint (Bucharest in first 7 days)
    solver.add(z3.Or([presence[i][0] for i in range(7)]))
    
    # Connectivity between consecutive days
    for i in range(15):
        solver.add(z3.Or(
            z3.And(presence[i][0], presence[i+1][0]),  # Stay in Bucharest
            z3.And(presence[i][1], presence[i+1][1]),  # Stay in Lyon
            z3.And(presence[i][2], presence[i+1][2]),  # Stay in Porto
            # Bucharest to Lyon transition
            z3.And(presence[i][0], presence[i+1][0], presence[i+1][1]),
            # Lyon to Porto transition
            z3.And(presence[i][1], presence[i+1][1], presence[i+1][2])
        ))
    
    # Solve and process solution
    if solver.check() == z3.sat:
        model = solver.model()
        city_names = ["Bucharest", "Lyon", "Porto"]
        daily_status = []
        
        # Determine city presence for each day
        for i in range(16):
            cities_present = []
            for j in range(3):
                if z3.is_true(model.evaluate(presence[i][j])):
                    cities_present.append(city_names[j])
            daily_status.append(cities_present)
        
        # Generate itinerary segments
        itinerary = []
        start_day = 0
        current_set = daily_status[0]
        
        for i in range(1, 16):
            if daily_status[i] == current_set:
                continue
            else:
                end_day = i - 1
                if start_day == end_day:
                    day_range = f"Day {start_day+1}"
                else:
                    day_range = f"Day {start_day+1}-{end_day+1}"
                
                place = " and ".join(sorted(current_set))
                itinerary.append({"day_range": day_range, "place": place})
                
                start_day = i
                current_set = daily_status[i]
        
        # Add last segment
        if start_day == 15:
            day_range = f"Day {16}"
        else:
            day_range = f"Day {start_day+1}-16"
        place = " and ".join(sorted(daily_status[15]))
        itinerary.append({"day_range": day_range, "place": place})
        
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()