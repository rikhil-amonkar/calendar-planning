from z3 import *
import json

def solve_itinerary():
    # Total days
    total_days = 18
    
    # Required days in each city
    split_days = 6
    santorini_days = 7
    london_days = 7
    
    # Conference days in Santorini
    conference_days = [12, 18]
    
    # Cities and possible transitions
    cities = ['Split', 'Santorini', 'London']
    direct_flights = {
        'Split': ['London'],
        'Santorini': ['London'],
        'London': ['Split', 'Santorini']
    }
    
    # Create Z3 variables for each day's city
    day_city = [Int(f'day_{i}_city') for i in range(1, total_days + 1)]
    
    # City encodings
    city_encoding = {'Split': 0, 'Santorini': 1, 'London': 2}
    reverse_city_encoding = {0: 'Split', 1: 'Santorini', 2: 'London'}
    
    s = Solver()
    
    # Each day must be one of the three cities
    for i in range(total_days):
        s.add(Or(day_city[i] == 0, day_city[i] == 1, day_city[i] == 2))
    
    # Conference days must be in Santorini
    for day in conference_days:
        s.add(day_city[day - 1] == city_encoding['Santorini'])
    
    # Total days in each city
    s.add(Sum([If(day_city[i] == city_encoding['Split'], 1, 0) for i in range(total_days)]) == split_days)
    s.add(Sum([If(day_city[i] == city_encoding['Santorini'], 1, 0) for i in range(total_days)]) == santorini_days)
    s.add(Sum([If(day_city[i] == city_encoding['London'], 1, 0) for i in range(total_days)]) == london_days)
    
    # Flight constraints: consecutive days can only transition via direct flights
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # If staying in the same city, no problem
        s.add(Or(current_city == next_city,
                 # Or transition via direct flight
                 And(current_city != next_city,
                     Or(
                         And(current_city == city_encoding['Split'], next_city == city_encoding['London']),
                         And(current_city == city_encoding['London'], next_city == city_encoding['Split']),
                         And(current_city == city_encoding['London'], next_city == city_encoding['Santorini']),
                         And(current_city == city_encoding['Santorini'], next_city == city_encoding['London'])
                     )
                 )
             ))
    
    # Add constraint to ensure we don't have impossible sequences
    # For example, can't go directly from Split to Santorini
    for i in range(total_days - 1):
        s.add(Not(And(day_city[i] == city_encoding['Split'], day_city[i + 1] == city_encoding['Santorini'])))
        s.add(Not(And(day_city[i] == city_encoding['Santorini'], day_city[i + 1] == city_encoding['Split'])))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        itinerary_days = [m.evaluate(day_city[i]).as_long() for i in range(total_days)]
        itinerary_cities = [reverse_city_encoding[itinerary_days[i]] for i in range(total_days)]
        
        # Generate the itinerary in the required format
        itinerary = []
        current_city = itinerary_cities[0]
        start_day = 1
        
        for i in range(1, total_days):
            if itinerary_cities[i] == current_city:
                continue
            else:
                end_day = i
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": current_city})
                
                # Flight day: add departure and arrival
                departure_day = end_day + 1
                arrival_day = end_day + 1
                arrival_city = itinerary_cities[i]
                
                itinerary.append({"day_range": f"Day {departure_day}", "place": current_city})
                itinerary.append({"day_range": f"Day {arrival_day}", "place": arrival_city})
                
                current_city = arrival_city
                start_day = i + 1
        
        # Add the last segment
        end_day = total_days
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))