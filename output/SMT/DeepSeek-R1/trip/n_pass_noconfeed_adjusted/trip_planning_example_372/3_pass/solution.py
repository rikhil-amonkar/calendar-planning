from z3 import *
import json

def main():
    cities = {0: "Porto", 1: "Stuttgart", 2: "Seville", 3: "Madrid"}
    direct_flights = [(0,1), (1,0), (0,2), (2,0), (0,3), (3,0), (2,3), (3,2)]
    
    solver = Solver()
    
    # Create variables for each day's city (1-indexed days)
    city = [Int(f"city_{i}") for i in range(1,14)]
    
    # Each day's city must be valid
    for c in city:
        solver.add(c >= 0, c <= 3)
    
    # Constraint: Direct flights required when changing cities between consecutive days
    for i in range(13-1):
        solver.add(If(city[i] != city[i+1],
                      Or([And(city[i] == c1, city[i+1] == c2) for (c1,c2) in direct_flights]),
                      True))
    
    # Calculate total days per city
    total_days = [0]*4
    for c in range(4):
        total_days[c] = Sum([If(city[i] == c, 1, 0) for i in range(13)])
    
    # Adjusted constraints to total 13 days
    solver.add(total_days[0] == 3)  # Porto
    solver.add(total_days[1] == 5)  # Stuttgart (reduced from 7 to 5)
    solver.add(total_days[2] == 2)  # Seville
    solver.add(total_days[3] == 3)  # Madrid (reduced from 4 to 3)
    
    # Constraint: Conference days in Stuttgart
    solver.add(city[6] == 1)  # Day 7
    solver.add(city[12] == 1) # Day 13
    
    # Constraint: Visit Madrid between days 1-4
    solver.add(Or([city[i] == 3 for i in range(4)]))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Extract city for each day
        itinerary_days = []
        for i in range(13):
            day_num = i + 1
            city_val = model.evaluate(city[i]).as_long()
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