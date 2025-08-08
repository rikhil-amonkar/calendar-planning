from z3 import *
import json

def main():
    # Define cities and required stay durations
    cities = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
    req_days = {
        "Paris": 5,
        "Florence": 3,
        "Vienna": 2,
        "Porto": 3,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3
    }
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        ("Florence", "Vienna"), ("Paris", "Warsaw"), ("Munich", "Vienna"),
        ("Porto", "Vienna"), ("Warsaw", "Vienna"), ("Florence", "Munich"),
        ("Munich", "Warsaw"), ("Munich", "Nice"), ("Paris", "Florence"),
        ("Warsaw", "Nice"), ("Porto", "Munich"), ("Porto", "Nice"),
        ("Paris", "Vienna"), ("Nice", "Vienna"), ("Porto", "Paris"),
        ("Paris", "Nice"), ("Paris", "Munich"), ("Porto", "Warsaw")
    ]
    
    # Create Z3 variables for each day's location
    loc = [Int(f'loc_{i}') for i in range(20)]
    s = Solver()
    
    # Map cities to integer IDs
    city_ids = {city: idx for idx, city in enumerate(cities)}
    
    # Constraint: Each day's location must be a valid city ID (0-6)
    for i in range(20):
        s.add(loc[i] >= 0, loc[i] < len(cities))
    
    # Fixed event constraints
    s.add(loc[0] == city_ids["Porto"])   # Day 1: Porto
    s.add(loc[1] == city_ids["Porto"])   # Day 2: Porto
    s.add(loc[2] == city_ids["Porto"])   # Day 3: Porto
    s.add(loc[12] == city_ids["Warsaw"]) # Day 13: Warsaw
    s.add(loc[13] == city_ids["Warsaw"]) # Day 14: Warsaw
    s.add(loc[14] == city_ids["Warsaw"]) # Day 15: Warsaw
    s.add(loc[18] == city_ids["Vienna"]) # Day 19: Vienna
    s.add(loc[19] == city_ids["Vienna"]) # Day 20: Vienna
    
    # Flight constraints between consecutive days
    for i in range(19):
        current = loc[i]
        next_day = loc[i+1]
        
        # Either stay in the same city or take a direct flight
        s.add(Or(
            current == next_day,  # No flight
            # Check all possible direct flights
            Or([And(current == city_ids[a], next_day == city_ids[b]) 
               for a, b in direct_flights] + 
              [And(current == city_ids[b], next_day == city_ids[a]) 
               for a, b in direct_flights])
        ))
    
    # Total days per city constraint
    for city, days in req_days.items():
        cid = city_ids[city]
        total = Sum([If(loc[i] == cid, 1, 0) for i in range(20)])
        s.add(total == days)
    
    # Solve and build itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # First pass: get base locations
        base_plan = []
        for i in range(20):
            city_idx = m.eval(loc[i]).as_long()
            base_plan.append(cities[city_idx])
        
        # Second pass: add flight destinations to departure days
        for i in range(19):
            if base_plan[i] != base_plan[i+1]:
                # Add destination city to departure day
                if i in itinerary:
                    itinerary[i]["place"].append(base_plan[i+1])
                else:
                    itinerary.append({
                        "day": i+1,
                        "place": sorted([base_plan[i], base_plan[i+1]])
                    })
        
        # Add days without flights
        for i in range(20):
            if not any(entry["day"] == i+1 for entry in itinerary):
                itinerary.append({"day": i+1, "place": [base_plan[i]]})
        
        # Sort by day number
        itinerary.sort(key=lambda x: x["day"])
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()