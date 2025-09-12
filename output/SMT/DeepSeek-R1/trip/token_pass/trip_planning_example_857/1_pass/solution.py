import json
from z3 import *

def main():
    # Define the cities with indices
    cities = {
        'Porto': 0,
        'Geneva': 1,
        'Mykonos': 2,
        'Manchester': 3,
        'Hamburg': 4,
        'Naples': 5,
        'Frankfurt': 6
    }
    inv_cities = {v: k for k, v in cities.items()}
    
    # Direct flights as symmetric pairs
    direct_flights = [
        (4, 6), (5, 2), (4, 0), (4, 1), (2, 1),
        (6, 1), (6, 0), (1, 0), (1, 3), (5, 3),
        (6, 5), (6, 3), (5, 1), (0, 3), (4, 3)
    ]
    # Make sure both directions are considered
    allowed_pairs = set()
    for a, b in direct_flights:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Total days
    total_days = 18
    solver = Solver()
    
    # Morning and evening city for each day (0-indexed)
    morning = [Int(f'm_{i}') for i in range(total_days)]
    evening = [Int(f'e_{i}') for i in range(total_days)]
    
    # Constraint: Each city value is between 0 and 6
    for i in range(total_days):
        solver.add(And(morning[i] >= 0, morning[i] <= 6))
        solver.add(And(evening[i] >= 0, evening[i] <= 6))
    
    # Constraint: Evening city equals next morning city
    for i in range(total_days - 1):
        solver.add(evening[i] == morning[i+1])
    
    # Constraint: If morning and evening differ, must have direct flight
    for i in range(total_days):
        solver.add(If(
            morning[i] != evening[i],
            Or([And(morning[i] == a, evening[i] == b) for (a, b) in allowed_pairs]),
            True
        ))
    
    # Total days per city constraints
    city_days = [
        (0, 2),  # Porto
        (1, 3),  # Geneva
        (2, 3),  # Mykonos
        (3, 4),  # Manchester
        (4, 5),  # Hamburg
        (5, 5),  # Naples
        (6, 2)   # Frankfurt
    ]
    for city, required_days in city_days:
        count = 0
        for i in range(total_days):
            count += If(morning[i] == city, 1, 0)
            count += If(evening[i] == city, 1, 0)
        solver.add(count == required_days)
    
    # Event constraints
    # Mykonos between day 10 and 12 (indices 9, 10, 11)
    solver.add(Or(
        Or([morning[i] == cities['Mykonos'] for i in [9, 10, 11]]),
        Or([evening[i] == cities['Mykonos'] for i in [9, 10, 11]])
    ))
    
    # Manchester between day 15 and 18 (indices 14, 15, 16, 17)
    solver.add(Or(
        Or([morning[i] == cities['Manchester'] for i in [14, 15, 16, 17]]),
        Or([evening[i] == cities['Manchester'] for i in [14, 15, 16, 17]])
    ))
    
    # Frankfurt on day 5 and 6 (indices 4 and 5)
    solver.add(Or(
        morning[4] == cities['Frankfurt'],
        evening[4] == cities['Frankfurt']
    ))
    solver.add(Or(
        morning[5] == cities['Frankfurt'],
        evening[5] == cities['Frankfurt']
    ))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        morning_vals = [model.evaluate(morning[i]).as_long() for i in range(total_days)]
        evening_vals = [model.evaluate(evening[i]).as_long() for i in range(total_days)]
        
        # Reconstruct itinerary segments
        itinerary = []
        current_city = inv_cities[morning_vals[0]]
        start_day = 1
        start_part = "morning"
        
        # Process each day part
        for day in range(total_days):
            day_num = day + 1
            # Check morning
            morning_city = inv_cities[morning_vals[day]]
            if morning_city != current_city:
                # End previous segment
                end_day = day_num if start_part == "morning" else day_num - 1
                if start_day == end_day:
                    itinerary.append({
                        "day_range": f"Day {start_day} {start_part}",
                        "place": current_city
                    })
                else:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": current_city
                    })
                # Start new segment for morning
                current_city = morning_city
                start_day = day_num
                start_part = "morning"
            
            # Check evening
            evening_city = inv_cities[evening_vals[day]]
            if evening_city != current_city:
                # End current segment (morning part of the day)
                itinerary.append({
                    "day_range": f"Day {day_num} morning",
                    "place": current_city
                })
                # Start new segment for evening
                current_city = evening_city
                start_day = day_num
                start_part = "evening"
        
        # Add the last segment
        end_day = total_days
        if start_part == "morning":
            end_day = total_days
        else:
            end_day = total_days
        if start_day == end_day:
            itinerary.append({
                "day_range": f"Day {start_day} {start_part}",
                "place": current_city
            })
        else:
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": current_city
            })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()