import z3
import json

def main():
    # City codes
    cities = {
        "Oslo": 0,
        "Reykjavik": 1,
        "Stockholm": 2,
        "Munich": 3,
        "Frankfurt": 4,
        "Barcelona": 5,
        "Bucharest": 6,
        "Split": 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Required days per city
    required_days = {
        cities["Oslo"]: 2,
        cities["Reykjavik"]: 5,
        cities["Stockholm"]: 4,
        cities["Munich"]: 4,
        cities["Frankfurt"]: 4,
        cities["Barcelona"]: 3,
        cities["Bucharest"]: 2,
        cities["Split"]: 3
    }
    
    # Allowed direct flights (as sorted tuples)
    allowed_edges = {
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
        (1, 2), (1, 3), (1, 4), (1, 5),
        (2, 3), (2, 4), (2, 5), (2, 7),
        (3, 4), (3, 5), (3, 6), (3, 7),
        (4, 5), (4, 6), (4, 7),
        (5, 6), (5, 7)
    }
    
    # Create morning and afternoon arrays for 20 days
    morning = [z3.Int(f'morning_{i}') for i in range(20)]
    afternoon = [z3.Int(f'afternoon_{i}') for i in range(20)]
    
    solver = z3.Solver()
    
    # Constraint: each day's morning and afternoon are valid cities
    for i in range(20):
        solver.add(z3.And(morning[i] >= 0, morning[i] <= 7))
        solver.add(z3.And(afternoon[i] >= 0, afternoon[i] <= 7))
    
    # Flight constraint: if morning != afternoon, must have direct flight
    for i in range(20):
        morning_city = morning[i]
        afternoon_city = afternoon[i]
        edge = z3.And(morning_city != afternoon_city)
        allowed = z3.Or([z3.And(morning_city == a, afternoon_city == b) for a, b in allowed_edges] +
                        [z3.And(morning_city == b, afternoon_city == a) for a, b in allowed_edges])
        solver.add(z3.Implies(edge, allowed))
    
    # Presence for each city each day: city appears in morning or afternoon
    presence = [[z3.Or(morning[i] == c, afternoon[i] == c) for i in range(20)] for c in range(8)]
    
    # Total days per city
    for c in range(8):
        solver.add(z3.Sum([z3.If(presence[c][i], 1, 0) for i in range(20)]) == required_days[c])
    
    # Specific constraints
    # Oslo on day 16 and 17 (indices 15 and 16)
    solver.add(presence[0][15] == True)
    solver.add(presence[0][16] == True)
    
    # Reykjavik between day 9 and 13 (indices 8 to 12)
    solver.add(z3.Or([presence[1][i] for i in range(8, 13)]))
    
    # Munich between day 13 and 16 (indices 12 to 15)
    solver.add(z3.Or([presence[3][i] for i in range(12, 16)]))
    
    # Frankfurt between day 17 and 20 (indices 16 to 19)
    solver.add(z3.Or([presence[4][i] for i in range(16, 20)]))
    
    # Check and get model
    if solver.check() == z3.sat:
        model = solver.model()
        afternoon_values = [model.evaluate(afternoon[i]).as_long() for i in range(20)]
        
        # Group consecutive days with same afternoon city
 itinerary = []
        start = 1
        current_city = afternoon_values[0]
        for day in range(1, 20):
            if afternoon_values[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start}-{end_day}",
                    "place": city_names[current_city]
                })
                start = day + 1
                current_city = afternoon_values[day]
        itinerary.append({
            "day_range": f"Day {start}-20",
            "place": city_names[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()