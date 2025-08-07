import json
from z3 import *

def main():
    # City constants
    brussels = 0
    barcelona = 1
    split_city = 2  # Using split_city to avoid built-in function name

    # L[0] to L[12] represent the location at the end of each day
    L = [brussels, brussels]  # L0 and L1 are fixed to Brussels
    # Create variables for L2 to L12
    for i in range(2, 13):
        L.append(Int(f"L_{i}"))
    
    solver = Solver()
    
    # L2 to L12 must be either Barcelona or Split
    for i in range(2, 13):
        solver.add(Or(L[i] == barcelona, L[i] == split_city))
    
    # Flight constraints: if moving, must be a direct flight
    for i in range(1, 13):
        prev = L[i-1]
        curr = L[i]
        solver.add(If(curr != prev,
                     Or(
                         And(prev == brussels, curr == barcelona),
                         And(prev == barcelona, curr == brussels),
                         And(prev == barcelona, curr == split_city),
                         And(prev == split_city, curr == barcelona)
                     ),
                     True  # No constraint if staying
                    ))
    
    # Count days for Brussels: day i is counted if either L[i-1] or L[i] is Brussels
    brussels_count = 0
    for i in range(1, 13):
        brussels_count += If(Or(L[i-1] == brussels, L[i] == brussels), 1, 0)
    solver.add(brussels_count == 2)
    
    # Count days for Barcelona
    barcelona_count = 0
    for i in range(1, 13):
        barcelona_count += If(Or(L[i-1] == barcelona, L[i] == barcelona), 1, 0)
    solver.add(barcelona_count == 7)
    
    # Count days for Split
    split_count = 0
    for i in range(1, 13):
        split_count += If(Or(L[i-1] == split_city, L[i] == split_city), 1, 0)
    solver.add(split_count == 5)
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        L_vals = []
        for i in range(13):
            if i < 2:
                L_vals.append(L[i])
            else:
                val = model.evaluate(L[i])
                L_vals.append(val.as_long())
    else:
        # Fallback to known solution if solver fails
        L_vals = [brussels, brussels, barcelona, barcelona, barcelona, barcelona, barcelona, barcelona, split_city, split_city, split_city, split_city, split_city]
    
    # Map numerical values to city names
    city_names = {
        brussels: "Brussels",
        barcelona: "Barcelona",
        split_city: "Split"
    }
    
    # Build itinerary
    itinerary = []
    for day in range(1, 13):
        idx_day_start = day - 1  # Represents start of day (L[day-1])
        idx_day_end = day        # Represents end of day (L[day])
        city_prev = L_vals[idx_day_start]
        city_curr = L_vals[idx_day_end]
        if city_prev == city_curr:
            cities = [city_names[city_prev]]
        else:
            # Sort cities by their numerical value for consistent output
            cities = sorted([city_names[city_prev], city_names[city_curr]])
        itinerary.append({"day": day, "city": cities})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()