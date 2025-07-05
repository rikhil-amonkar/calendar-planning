from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    
    # Direct flights (undirected except Reykjavik -> Madrid)
    direct_flights = {
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')  # Note: only from Reykjavik to Madrid
    }
    
    # Make sure flights are bidirectional except Reykjavik -> Madrid
    all_flights = set()
    for (a, b) in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    # Remove Madrid -> Reykjavik if it's one-way
    if ('Madrid', 'Reykjavik') in all_flights:
        all_flights.remove(('Madrid', 'Reykjavik'))
    
    # Total days
    total_days = 14
    
    # Create Z3 variables: for each day, which city are we in?
    day_city = [Int(f'day_{i}_city') for i in range(1, total_days + 1)]
    
    # City to integer mapping
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    s = Solver()
    
    # Each day's city must be valid (0 to 5)
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Flight constraints: consecutive days must be connected by a flight or same city
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either same city or connected by flight
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_int[a], next_city == city_to_int[b]) 
              for (a, b) in all_flights]
        ))
    
    # Total days per city constraints
    for city in cities:
        count = 0
        for day in day_city:
            count += If(day == city_to_int[city], 1, 0)
        if city == 'Helsinki':
            s.add(count == 2)
        elif city == 'Warsaw':
            s.add(count == 3)
        elif city == 'Madrid':
            s.add(count == 4)
        elif city == 'Split':
            s.add(count == 4)
        elif city == 'Reykjavik':
            s.add(count == 2)
        elif city == 'Budapest':
            s.add(count == 4)
    
    # Fixed events:
    # Helsinki: workshop between day 1 and day 2 → must be in Helsinki on day 1 or day 2 or both.
    s.add(Or(day_city[0] == city_to_int['Helsinki'], day_city[1] == city_to_int['Helsinki']))
    
    # Warsaw: relatives between day 9 and day 11 (inclusive) → must be in Warsaw on at least one of days 9, 10, or 11.
    s.add(Or(
        day_city[8] == city_to_int['Warsaw'],  # day 9 is index 8 (0-based)
        day_city[9] == city_to_int['Warsaw'],  # day 10
        day_city[10] == city_to_int['Warsaw']  # day 11
    ))
    
    # Reykjavik: friend between day 8 and day 9 → must be in Reykjavik on day 8 or day 9.
    s.add(Or(
        day_city[7] == city_to_int['Reykjavik'],  # day 8
        day_city[8] == city_to_int['Reykjavik']   # day 9
    ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        sequence = []
        for day in day_city:
            city_idx = m.evaluate(day).as_long()
            sequence.append(int_to_city[city_idx])
        
        # Generate the itinerary
        itinerary = []
        current_place = sequence[0]
        start_day = 1
        
        for day in range(1, total_days):
            if sequence[day] != current_place:
                # Flight occurs on day+1 (1-based)
                # Add the stay in current_place from start_day to day (0-based is day-1 in 1-based)
                end_day = day
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": current_place})
                
                # Add flight day entries
                flight_day = day + 1
                itinerary.append({"day_range": f"Day {flight_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {flight_day}", "place": sequence[day]})
                
                # Update current_place and start_day
                current_place = sequence[day]
                start_day = flight_day
        
        # Add the last segment
        end_day = total_days
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": current_place})
        
        return json.dumps({"itinerary": itinerary}, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

print(solve_itinerary())