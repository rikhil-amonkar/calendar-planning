from z3 import *
import json

def main():
    # Define cities and their required stay days
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
    
    # Create flight set for quick lookup
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    # Create Z3 variables - one per day
    loc = [Int(f'loc_{i}') for i in range(20)]  # Day 0 to 19
    
    s = Solver()
    
    # City mapping: assign each city an integer ID
    city_ids = {city: i for i, city in enumerate(cities)}
    for i in range(20):
        s.add(loc[i] >= 0, loc[i] < len(cities))
    
    # Flight constraints: consecutive days must be same city or have direct flight
    for i in range(19):
        current = loc[i]
        next_day = loc[i+1]
        # Create OR condition for valid transitions
        transitions = []
        for c1 in cities:
            for c2 in cities:
                if c1 == c2 or (c1, c2) in flight_set:
                    transitions.append(
                        And(current == city_ids[c1], next_day == city_ids[c2])
                    )
        s.add(Or(transitions))
    
    # Fixed events constraints
    s.add(loc[0] == city_ids["Porto"])  # Day 1: Porto
    s.add(loc[1] == city_ids["Porto"])  # Day 2: Porto
    s.add(loc[2] == city_ids["Porto"])  # Day 3: Porto
    
    # Warsaw wedding days 13-15 (index 12-14)
    s.add(loc[12] == city_ids["Warsaw"])
    s.add(loc[13] == city_ids["Warsaw"])
    s.add(loc[14] == city_ids["Warsaw"])
    
    # Vienna relatives days 19-20 (index 18-19)
    s.add(loc[18] == city_ids["Vienna"])
    s.add(loc[19] == city_ids["Vienna"])
    
    # Total days per city
    for city in cities:
        count = 0
        for i in range(20):
            count += If(loc[i] == city_ids[city], 1, 0)
        s.add(count == req_days[city])
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(20):
            city_id = m.eval(loc[day]).as_long()
            itinerary.append({
                "day": day + 1,
                "place": [cities[city_id]]
            })
        
        # Add flight days (days where city changes)
        for i in range(19):
            curr_city = m.eval(loc[i]).as_long()
            next_city = m.eval(loc[i+1]).as_long()
            if curr_city != next_city:
                # Add next city to current day's places
                itinerary[i]["place"].append(cities[next_city])
                # Sort alphabetically
                itinerary[i]["place"].sort()
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()