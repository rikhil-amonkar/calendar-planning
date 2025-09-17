from z3 import *
import json

def main():
    # Cities encoding: Porto=0, Stuttgart=1, Seville=2, Madrid=3
    cities = {0: "Porto", 1: "Stuttgart", 2: "Seville", 3: "Madrid"}
    direct_flights = [(0,1), (1,0), (0,2), (2,0), (0,3), (3,0), (2,3), (3,2)]
    
    solver = Solver()
    
    # Create variables for start and end cities for each day (1-indexed)
    start_city = [Int(f"start_{i}") for i in range(1,14)]
    end_city = [Int(f"end_{i}") for i in range(1,14)]
    
    # Constraint: Each city variable must be between 0 and 3
    for i in range(13):
        solver.add(start_city[i] >= 0, start_city[i] <= 3)
        solver.add(end_city[i] >= 0, end_city[i] <= 3)
    
    # Constraint: Consistency between consecutive days
    for i in range(1,13):
        solver.add(end_city[i-1] == start_city[i])
    
    # Constraint: Direct flights required when cities change
    for i in range(13):
        solver.add(If(start_city[i] != end_city[i],
                      Or([And(start_city[i] == c1, end_city[i] == c2) for (c1,c2) in direct_flights]),
                      True))
    
    # Calculate total days per city (counting travel days)
    total_days = [0]*4
    for c in range(4):
        count = 0
        for i in range(13):
            # Count start city
            count += If(start_city[i] == c, 1, 0)
            # Count end city only if different from start (travel day)
            count += If(And(start_city[i] != end_city[i], end_city[i] == c), 1, 0)
        total_days[c] = count
    
    # Constraint: Required days per city
    solver.add(total_days[2] == 2)  # Seville
    solver.add(total_days[1] == 7)  # Stuttgart
    solver.add(total_days[0] == 3)  # Porto
    solver.add(total_days[3] == 4)  # Madrid
    
    # Constraint: Conference days in Stuttgart (no travel)
    solver.add(start_city[6] == 1, end_city[6] == 1)  # Day 7
    solver.add(start_city[12] == 1, end_city[12] == 1)  # Day 13
    
    # Constraint: Visit Madrid between days 1-4
    solver.add(Or([Or(start_city[i] == 3, end_city[i] == 3) for i in range(4)]))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Extract end city for each day
        itinerary_days = []
        for i in range(13):
            day_num = i + 1
            city_val = model.evaluate(end_city[i]).as_long()
            itinerary_days.append((day_num, cities[city_val]))
        
        # Group consecutive days with same city
        itinerary_json = []
        current_start = 1
        current_city = itinerary_days[0][1]
        
        for day in range(2, 14):
            if itinerary_days[day-1][1] != current_city:
                day_range = f"Day {current_start}-{day-1}" if current_start != day-1 else f"Day {current_start}"
                itinerary_json.append({"day_range": day_range, "place": current_city})
                current_start = day
                current_city = itinerary_days[day-1][1]
        
        day_range = f"Day {current_start}-13" if current_start != 13 else "Day 13"
        itinerary_json.append({"day_range": day_range, "place": current_city})
        
        print(json.dumps({"itinerary": itinerary_json}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()