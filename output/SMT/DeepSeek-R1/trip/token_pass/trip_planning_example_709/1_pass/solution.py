import z3
import json

def main():
    # City mapping
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    req_days = [4, 5, 4, 3, 3, 4]
    allowed_flights = [(0,4), (4,0), (4,1), (1,4), (1,3), (3,1), (0,5), (5,0), (2,0), (0,2), (5,4), (4,5)]
    
    # Create solver and variables
    s = z3.Solver()
    c = [z3.Int('c_%d' % i) for i in range(19)]
    
    # Add constraints for city indices
    for i in range(19):
        s.add(z3.And(c[i] >= 0, c[i] <= 5))
    
    # Add flight constraints
    for i in range(1, 19):
        s.add(z3.Or([z3.And(c[i-1] == a, c[i] == b) for (a,b) in allowed_flights] + [c[i-1] == c[i]]))
    
    # Add day count constraints
    for city_idx in range(6):
        total = 0
        for day in range(1, 19):
            total += z3.If(z3.Or(c[day-1] == city_idx, c[day] == city_idx), 1, 0)
        s.add(total == req_days[city_idx])
    
    # Add Porto meeting constraint
    porto_constraint = z3.Or([z3.Or(c[day-1] == 3, c[day] == 3) for day in range(16, 19)])
    s.add(porto_constraint)
    
    # Solve and output
    if s.check() == z3.sat:
        m = s.model()
        seq = [m.evaluate(c[i]).as_long() for i in range(19)]
        
        # Generate itinerary
        itinerary = []
        current_city = seq[0]
        start_day = 1
        for day in range(1, 19):
            if seq[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                current_city = seq[day]
                start_day = day
        itinerary.append({
            "day_range": f"Day {start_day}-18",
            "place": cities[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()