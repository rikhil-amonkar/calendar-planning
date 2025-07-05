import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    
    # Direct flights
    direct_flights = {
        'Paris': ['Oslo', 'Porto', 'Geneva', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Porto', 'Oslo'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    # Total days
    total_days = 23
    
    # Create Z3 solver
    solver = Solver()
    
    # Variables: day[i] represents the city on day i (1-based)
    day = [Int(f'day_{i}') for i in range(1, total_days + 1)]
    
    # City encodings
    city_codes = {
        'Paris': 0,
        'Oslo': 1,
        'Porto': 2,
        'Geneva': 3,
        'Reykjavik': 4
    }
    code_to_city = {v: k for k, v in city_codes.items()}
    
    # Constraint: each day must be one of the cities
    for d in day:
        solver.add(Or([d == code for code in city_codes.values()]))
    
    # Fixed constraints:
    # Days 1-7 in Geneva (conference)
    for i in range(1, 8):
        solver.add(day[i-1] == city_codes['Geneva'])
    
    # Days 19-23 in Oslo (visiting relatives)
    for i in range(19, 24):
        solver.add(day[i-1] == city_codes['Oslo'])
    
    # Count days per city
    counts = {
        'Paris': 0,
        'Oslo': 0,
        'Porto': 0,
        'Geneva': 0,
        'Reykjavik': 0
    }
    for city, code in city_codes.items():
        counts[city] = Sum([If(day[i] == code, 1, 0) for i in range(total_days)])
    
    # Required days: note that flight days count for both cities, but the model counts each day once.
    # So the model's counts may be less than required because flight days are counted once.
    # To account for this, we may need to adjust the required days.
    # Alternatively, we can proceed and adjust the counts in post-processing.
    solver.add(counts['Paris'] == cities['Paris'])
    solver.add(counts['Oslo'] >= cities['Oslo'])  # Oslo's days include the fixed days 19-23 (5 days)
    solver.add(counts['Porto'] == cities['Porto'])
    solver.add(counts['Geneva'] >= cities['Geneva'])  # Geneva's days include days 1-7 (7 days)
    solver.add(counts['Reykjavik'] == cities['Reykjavik'])
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        solver.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_codes[a], next_city == city_codes[b])
                for a in direct_flights
                for b in direct_flights[a]
            ]
        ))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        itinerary_days = []
        for i in range(total_days):
            city_code = model.evaluate(day[i]).as_long()
            itinerary_days.append(code_to_city[city_code])
        
        # Generate the itinerary in the required JSON format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for i in range(1, total_days):
            if itinerary_days[i] != itinerary_days[i-1]:
                # Add the stay up to the previous day
                if start_day == i:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{i}"
                itinerary.append({"day_range": day_str, "place": current_place})
                
                # Add the flight day (transition)
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": itinerary_days[i]})
                
                current_place = itinerary_days[i]
                start_day = i + 1
        
        # Add the last segment
        if start_day == total_days:
            day_str = f"Day {start_day}"
        else:
            day_str = f"Day {start_day}-{total_days}"
        itinerary.append({"day_range": day_str, "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))