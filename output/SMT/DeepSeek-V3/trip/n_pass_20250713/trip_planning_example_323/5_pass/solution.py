from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['London', 'Oslo', 'Split', 'Porto']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    n_days = 16
    
    # Z3 variables: day_1 to day_16 represent the city indices (0 to 3)
    day_vars = [Int(f'day_{i}') for i in range(1, n_days + 1)]
    
    s = Solver()
    
    # Each day variable must be a valid city index
    for day in day_vars:
        s.add(day >= 0, day <= 3)
    
    # Flight connections: possible transitions between cities
    for i in range(n_days - 1):
        current = day_vars[i]
        next_ = day_vars[i + 1]
        s.add(Or(
            # London (0) connected to Oslo (1) and Split (2)
            And(current == 0, Or(next_ == 1, next_ == 2)),
            # Oslo (1) connected to London (0), Split (2), Porto (3)
            And(current == 1, Or(next_ == 0, next_ == 2, next_ == 3)),
            # Split (2) connected to London (0) and Oslo (1)
            And(current == 2, Or(next_ == 0, next_ == 1)),
            # Porto (3) connected to Oslo (1)
            And(current == 3, next_ == 1),
            current == next_  # Stay in the same city
        ))
    
    # Count days in each city (including flight days)
    london_days = Sum([If(day_vars[i] == city_indices['London'], 1, 0) for i in range(n_days)])
    oslo_days = Sum([If(day_vars[i] == city_indices['Oslo'], 1, 0) for i in range(n_days)])
    split_days = Sum([If(day_vars[i] == city_indices['Split'], 1, 0) for i in range(n_days)])
    porto_days = Sum([If(day_vars[i] == city_indices['Porto'], 1, 0) for i in range(n_days)])
    
    # Count flight days (when city changes)
    flight_days = Sum([If(day_vars[i] != day_vars[i+1], 1, 0) for i in range(n_days - 1)])
    
    # Total days constraint (each flight day counts for 2 cities)
    s.add(london_days + oslo_days + split_days + porto_days - flight_days == n_days)
    
    # City day requirements
    s.add(london_days >= 7)
    s.add(oslo_days >= 2)
    s.add(split_days >= 5)
    s.add(porto_days >= 5)
    
    # Days 7-11 must be in Split
    for day in [6, 7, 8, 9, 10]:  # 0-based indexing
        s.add(day_vars[day] == city_indices['Split'])
    
    # At least one day in London between days 1-7 (0-based 0-6)
    s.add(Or([day_vars[i] == city_indices['London'] for i in range(7)]))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Extract the day assignments
        itinerary = []
        current_place = None
        start_day = 1
        for day in range(1, n_days + 1):
            city_idx = model.evaluate(day_vars[day - 1]).as_long()
            city = cities[city_idx]
            if day == 1:
                current_place = city
                start_day = 1
            else:
                prev_city_idx = model.evaluate(day_vars[day - 2]).as_long()
                prev_city = cities[prev_city_idx]
                if city != prev_city:
                    # Flight day
                    if start_day != day - 1:
                        itinerary.append({'day_range': f'Day {start_day}-{day - 1}', 'place': prev_city})
                    else:
                        itinerary.append({'day_range': f'Day {start_day}', 'place': prev_city})
                    itinerary.append({'day_range': f'Day {day}', 'place': prev_city})
                    itinerary.append({'day_range': f'Day {day}', 'place': city})
                    current_place = city
                    start_day = day
        # Add last segment
        if start_day != n_days:
            itinerary.append({'day_range': f'Day {start_day}-{n_days}', 'place': current_place})
        else:
            itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
        
        # Handle flight days where we need both cities
        transition_days = set()
        for day in range(1, n_days):
            if model.evaluate(day_vars[day - 1]).as_long() != model.evaluate(day_vars[day]).as_long():
                transition_days.add(day + 1)  # 1-based
        
        # Build final itinerary with proper flight days
        final_itinerary = []
        i = 0
        while i < len(itinerary):
            entry = itinerary[i]
            day_range = entry['day_range']
            place = entry['place']
            if '-' in day_range:
                final_itinerary.append(entry)
                i += 1
            else:
                day = int(day_range.split(' ')[1])
                if day in transition_days:
                    # Find previous city
                    prev_city = cities[model.evaluate(day_vars[day - 2]).as_long()]
                    # Add both cities for flight day
                    final_itinerary.append({'day_range': f'Day {day}', 'place': prev_city})
                    final_itinerary.append({'day_range': f'Day {day}', 'place': place})
                    i += 1
                else:
                    final_itinerary.append(entry)
                    i += 1
        
        return {'itinerary': final_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))