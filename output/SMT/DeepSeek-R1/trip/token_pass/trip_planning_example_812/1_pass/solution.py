import json
from z3 import *

def main():
    # City mapping
    city_names = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
    city_ids = {name: idx for idx, name in enumerate(city_names)}
    
    # Direct flights (as symmetric pairs)
    flight_pairs = [
        (1, 2), (0, 6), (4, 2), (3, 2), (6, 2), (1, 4), (4, 6), (4, 5),
        (0, 1), (6, 5), (3, 4), (3, 5), (0, 2), (5, 2), (3, 0), (0, 5),
        (0, 4), (3, 6)
    ]
    allowed_flights = set()
    for a, b in flight_pairs:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    
    solver = Solver()
    days = list(range(1, 21))
    
    # Create variables for start and end city for each day
    start_city = [Int(f'start_{i}') for i in days]
    end_city = [Int(f'end_{i}') for i in days]
    
    # Constraint: cities must be between 0 and 6
    for i in days:
        solver.add(And(start_city[i-1] >= 0, start_city[i-1] <= 6))
        solver.add(And(end_city[i-1] >= 0, end_city[i-1] <= 6))
    
    # Fixed constraints
    # Porto: days 1-3 start in Porto
    solver.add(start_city[0] == city_ids['Porto'])
    solver.add(start_city[1] == city_ids['Porto'])
    solver.add(start_city[2] == city_ids['Porto'])
    # Warsaw: days 13-15 start in Warsaw
    solver.add(start_city[12] == city_ids['Warsaw'])
    solver.add(start_city[13] == city_ids['Warsaw'])
    solver.add(start_city[14] == city_ids['Warsaw'])
    # Vienna: days 19-20 start and end in Vienna
    solver.add(start_city[18] == city_ids['Vienna'])
    solver.add(start_city[19] == city_ids['Vienna'])
    solver.add(end_city[18] == city_ids['Vienna'])
    solver.add(end_city[19] == city_ids['Vienna'])
    # Continuity constraints
    for i in range(1, 20):
        solver.add(start_city[i] == end_city[i-1])
    
    # Flight constraints
    for i in days:
        s = start_city[i-1]
        e = end_city[i-1]
        solver.add(If(s != e, 
                      Or([And(s == a, e == b) for (a, b) in allowed_flights]), 
                      True))
    
    # Constraints for end_city on day 3 and day 15
    solver.add(Or([end_city[2] == c for c in [0, 1, 4, 5]]))  # Must be Paris, Florence, Munich, or Nice
    solver.add(Or([end_city[14] == c for c in [0, 1, 4, 5]])) # Must be Paris, Florence, Munich, or Nice
    
    # Constraints: Vienna, Porto, Warsaw only appear on their fixed days
    # For days 4-12 and 16-18, ensure no Vienna, Porto, Warsaw
    other_days = list(range(3, 12)) + list(range(15, 18))  # day indices 3 to 11 and 15 to 17 (0-indexed)
    for i in other_days:
        solver.add(start_city[i] != city_ids['Vienna'])
        solver.add(end_city[i] != city_ids['Vienna'])
        solver.add(start_city[i] != city_ids['Porto'])
        solver.add(end_city[i] != city_ids['Porto'])
        solver.add(start_city[i] != city_ids['Warsaw'])
        solver.add(end_city[i] != city_ids['Warsaw'])
    
    # Total days constraints
    total_days = [0] * 7
    for c in range(7):
        total_days[c] = Sum([If(Or(start_city[i] == c, end_city[i] == c), 1, 0) for i in range(20)])
    solver.add(total_days[city_ids['Paris']] == 5)
    solver.add(total_days[city_ids['Florence']] == 3)
    solver.add(total_days[city_ids['Vienna']] == 2)
    solver.add(total_days[city_ids['Porto']] == 3)
    solver.add(total_days[city_ids['Munich']] == 5)
    solver.add(total_days[city_ids['Nice']] == 5)
    solver.add(total_days[city_ids['Warsaw']] == 3)
    
    # Check satisfaction
    if solver.check() == sat:
        model = solver.model()
        # Get the end city for each day
 itinerary_values = []
        for i in range(20):
            val = model.evaluate(end_city[i])
            itinerary_values.append(val.as_long())
        
        # Group consecutive days with the same end city
        itinerary = []
        current_city = itinerary_values[0]
        start_day = 1
        for day in range(1, 20):
            if itinerary_values[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": city_names[current_city]
                })
                start_day = day + 1
                current_city = itinerary_values[day]
        itinerary.append({
            "day_range": f"Day {start_day}-20",
            "place": city_names[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()