from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    
    # Direct flight connections
    direct_flights = {
        'Paris': ['Oslo', 'Geneva', 'Porto', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    # Create Z3 variables for each day's city
    day_vars = [Int(f'day_{day}') for day in range(1, 24)]
    city_ids = {city: idx for idx, city in enumerate(cities)}
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day_var in day_vars:
        s.add(day_var >= 0, day_var < len(cities))
    
    # Fixed periods
    # Days 1-7 in Geneva
    for day in range(1, 8):
        s.add(day_vars[day-1] == city_ids['Geneva'])
    
    # Days 19-23 in Oslo
    for day in range(19, 24):
        s.add(day_vars[day-1] == city_ids['Oslo'])
    
    # Flight constraints
    for day in range(1, 23):
        current_city = day_vars[day-1]
        next_city = day_vars[day]
        # If changing cities, ensure direct flight
        for city1 in cities:
            for city2 in cities:
                if city1 != city2 and city2 not in direct_flights[city1]:
                    s.add(Not(And(
                        current_city == city_ids[city1],
                        next_city == city_ids[city2]
                    )))
    
    # Total days per city
    for city, days in cities.items():
        s.add(Sum([If(day_var == city_ids[city], 1, 0) for day_var in day_vars]) == days)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        # Build itinerary from model
        for day in range(1, 24):
            city_idx = model.evaluate(day_vars[day-1]).as_long()
            city = list(cities.keys())[city_idx]
            
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Flight day - add both cities
                if start_day != day - 1:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day + 1
            elif day == 23:
                # Last day
                if start_day == day:
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))