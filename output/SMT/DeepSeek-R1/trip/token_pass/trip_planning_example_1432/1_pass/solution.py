import json
from z3 import *

def main():
    # Define cities and their indices
    cities = {
        "Frankfurt": 0,
        "Salzburg": 1,
        "Athens": 2,
        "Reykjavik": 3,
        "Bucharest": 4,
        "Valencia": 5,
        "Vienna": 6,
        "Amsterdam": 7,
        "Stockholm": 8,
        "Riga": 9
    }
    
    city_names = {v: k for k, v in cities.items()}
    
    # Required days per city
    required_days = {
        cities["Frankfurt"]: 4,
        cities["Salzburg"]: 5,
        cities["Athens"]: 5,
        cities["Reykjavik"]: 5,
        cities["Bucharest"]: 3,
        cities["Valencia"]: 2,
        cities["Vienna"]: 5,
        cities["Amsterdam"]: 3,
        cities["Stockholm"]: 3,
        cities["Riga"]: 3
    }
    
    # Direct flights (as provided)
    direct_flights_list = [
        (5, 0), (6, 4), (5, 2), (2, 4), (9, 0), (8, 2), (7, 4), (2, 9), (7, 0), (8, 6),
        (6, 9), (7, 3), (3, 0), (8, 7), (7, 5), (6, 0), (5, 4), (4, 0), (8, 0), (5, 6),
        (3, 2), (0, 1), (7, 6), (8, 3), (7, 9), (8, 9), (6, 3), (7, 2), (2, 0), (6, 2),
        (9, 4)
    ]
    
    # Create set of allowed flight connections (both directions)
    allowed_flights = set()
    for a, b in direct_flights_list:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    
    # Create solver
    solver = Solver()
    
    # Create variables for morning and evening cities for each day (1-indexed)
    morning = [Int(f'morning_{i}') for i in range(1, 30)]
    evening = [Int(f'evening_{i}') for i in range(1, 30)]
    
    # Constraints for each day
    for i in range(29):
        # Morning and evening must be valid cities
        solver.add(And(morning[i] >= 0, morning[i] <= 9))
        solver.add(And(evening[i] >= 0, evening[i] <= 9))
        
        # Evening of day i must equal morning of day i+1 (for i in [0, 27])
        if i < 28:
            solver.add(evening[i] == morning[i+1])
    
    # Travel constraints: if morning != evening, then flight must be allowed
    for i in range(29):
        solver.add(If(morning[i] != evening[i], 
                      Or([And(morning[i] == a, evening[i] == b) for (a, b) in allowed_flights]),
                      True))
    
    # Total days per city constraint
    for city_idx, req_days in required_days.items():
        total = 0
        for i in range(29):
            total += If(morning[i] == city_idx, 1, 0)
            total += If(evening[i] == city_idx, 1, 0)
        solver.add(total == req_days)
    
    # Specific constraints
    # Athens workshop between day 14-18 (inclusive)
    for day in range(14, 19):
        i = day - 1  # Convert to 0-indexed
        solver.add(Or(morning[i] == cities["Athens"], evening[i] == cities["Athens"]))
    
    # Valencia show on day 5 and 6
    for day in [5, 6]:
        i = day - 1
        solver.add(Or(morning[i] == cities["Valencia"], evening[i] == cities["Valencia"]))
    
    # Vienna wedding between day 6-10
    for day in range(6, 11):
        i = day - 1
        solver.add(Or(morning[i] == cities["Vienna"], evening[i] == cities["Vienna"]))
    
    # Stockholm meeting between day 1-3
    for day in range(1, 4):
        i = day - 1
        solver.add(Or(morning[i] == cities["Stockholm"], evening[i] == cities["Stockholm"]))
    
    # Riga conference between day 18-20
    for day in range(18, 21):
        i = day - 1
        solver.add(Or(morning[i] == cities["Riga"], evening[i] == cities["Riga"]))
    
    # Check feasibility
    if solver.check() == sat:
        model = solver.model()
        # Extract the evening cities for each day
        itinerary_days = []
        for i in range(29):
            city_val = model.evaluate(evening[i]).as_long()
            itinerary_days.append(city_names[city_val])
        
        # Group consecutive days with the same city
        grouped_itinerary = []
        start_day = 1
        current_city = itinerary_days[0]
        for day in range(2, 30):
            if itinerary_days[day-1] != current_city:
                end_day = day - 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                grouped_itinerary.append({"day_range": day_range, "place": current_city})
                start_day = day
                current_city = itinerary_days[day-1]
        # Add the last segment
        if start_day == 29:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-29"
        grouped_itinerary.append({"day_range": day_range, "place": current_city})
        
        # Output as JSON
        result = {"itinerary": grouped_itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()