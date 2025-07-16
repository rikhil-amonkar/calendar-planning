from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Dublin': 3,
        'Madrid': 2,
        'Oslo': 3,
        'London': 2,
        'Vilnius': 3,
        'Berlin': 5
    }
    city_list = list(cities.keys())
    city_to_int = {city: i for i, city in enumerate(city_list)}
    int_to_city = {i: city for i, city in enumerate(city_list)}
    
    # Direct flights (bidirectional)
    direct_flights = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Oslo': ['London', 'Madrid', 'Vilnius', 'Berlin', 'Dublin'],
        'Dublin': ['Madrid', 'Oslo', 'London', 'Berlin'],
        'Vilnius': ['Oslo', 'Berlin'],
        'Berlin': ['Madrid', 'Vilnius', 'Oslo', 'London', 'Dublin']
    }
    
    # Days 1 to 13
    num_days = 13
    days = [Int(f'day_{i}') for i in range(1, num_days + 1)]
    
    s = Solver()
    
    # Each day is assigned to a city (0 to 5)
    for day in days:
        s.add(day >= 0, day < len(city_list))
    
    # Total days per city
    for city in city_list:
        s.add(Sum([If(days[i] == city_to_int[city], 1, 0) for i in range(num_days)]) == cities[city])
    
    # Dublin includes at least one day in 7-9 (days 6-8 in zero-based)
    s.add(Or([days[i] == city_to_int['Dublin'] for i in range(6, 9)]))
    
    # Madrid includes day 2 or 3 (days 1 or 2 in zero-based)
    s.add(Or(days[1] == city_to_int['Madrid'], days[2] == city_to_int['Madrid']))
    
    # Berlin includes at least one day in 3-7 (days 2-6 in zero-based)
    s.add(Or([days[i] == city_to_int['Berlin'] for i in range(2, 7)]))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(num_days - 1):
        current_city = days[i]
        next_city = days[i + 1]
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == city_to_int[city], next_city == city_to_int[adj])
               for city in city_list for adj in direct_flights[city]])
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        day_assignments = [model.evaluate(day).as_long() for day in days]
        city_assignments = [int_to_city[i] for i in day_assignments]
        
        # Build itinerary
        itinerary = []
        current_city = city_assignments[0]
        start_day = 1
        
        for i in range(1, num_days):
            if city_assignments[i] != current_city:
                end_day = i
                itinerary.append({
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': current_city
                })
                # Add transition day records
                itinerary.append({
                    'day_range': f'Day {end_day}',
                    'place': current_city
                })
                itinerary.append({
                    'day_range': f'Day {end_day}',
                    'place': city_assignments[i]
                })
                current_city = city_assignments[i]
                start_day = i + 1
        
        # Add final segment
        itinerary.append({
            'day_range': f'Day {start_day}-{num_days}',
            'place': current_city
        })
        
        # Post-process to merge adjacent same-city entries
        merged_itinerary = []
        i = 0
        while i < len(itinerary):
            current = itinerary[i]
            if i + 1 < len(itinerary):
                next_entry = itinerary[i + 1]
                if current['place'] == next_entry['place']:
                    # Check if ranges are contiguous
                    current_end = int(current['day_range'].split('-')[-1])
                    next_start = int(next_entry['day_range'].split('-')[0][4:])
                    if next_start == current_end + 1:
                        # Merge
                        new_start = int(current['day_range'].split('-')[0][4:])
                        new_end = int(next_entry['day_range'].split('-')[-1])
                        merged_entry = {
                            'day_range': f'Day {new_start}-{new_end}',
                            'place': current['place']
                        }
                        merged_itinerary.append(merged_entry)
                        i += 2
                        continue
            merged_itinerary.append(current)
            i += 1
        
        return {'itinerary': merged_itinerary}
    else:
        # If still no solution, try relaxing the specific day constraints
        s.reset()
        for day in days:
            s.add(day >= 0, day < len(city_list))
        
        for city in city_list:
            s.add(Sum([If(days[i] == city_to_int[city], 1, 0) for i in range(num_days)]) == cities[city])
        
        for i in range(num_days - 1):
            current_city = days[i]
            next_city = days[i + 1]
            s.add(Or(
                current_city == next_city,
                Or([And(current_city == city_to_int[city], next_city == city_to_int[adj])
                   for city in city_list for adj in direct_flights[city]])
            ))
        
        if s.check() == sat:
            model = s.model()
            day_assignments = [model.evaluate(day).as_long() for day in days]
            city_assignments = [int_to_city[i] for i in day_assignments]
            
            itinerary = []
            current_city = city_assignments[0]
            start_day = 1
            
            for i in range(1, num_days):
                if city_assignments[i] != current_city:
                    end_day = i
                    itinerary.append({
                        'day_range': f'Day {start_day}-{end_day}',
                        'place': current_city
                    })
                    itinerary.append({
                        'day_range': f'Day {end_day}',
                        'place': current_city
                    })
                    itinerary.append({
                        'day_range': f'Day {end_day}',
                        'place': city_assignments[i]
                    })
                    current_city = city_assignments[i]
                    start_day = i + 1
            
            itinerary.append({
                'day_range': f'Day {start_day}-{num_days}',
                'place': current_city
            })
            
            merged_itinerary = []
            i = 0
            while i < len(itinerary):
                current = itinerary[i]
                if i + 1 < len(itinerary):
                    next_entry = itinerary[i + 1]
                    if current['place'] == next_entry['place']:
                        current_end = int(current['day_range'].split('-')[-1])
                        next_start = int(next_entry['day_range'].split('-')[0][4:])
                        if next_start == current_end + 1:
                            new_start = int(current['day_range'].split('-')[0][4:])
                            new_end = int(next_entry['day_range'].split('-')[-1])
                            merged_entry = {
                                'day_range': f'Day {new_start}-{new_end}',
                                'place': current['place']
                            }
                            merged_itinerary.append(merged_entry)
                            i += 2
                            continue
                merged_itinerary.append(current)
                i += 1
            
            return {'itinerary': merged_itinerary}
        else:
            return {'error': 'No valid itinerary could be found that satisfies all constraints'}

result = solve_itinerary()
print(json.dumps(result, indent=2))