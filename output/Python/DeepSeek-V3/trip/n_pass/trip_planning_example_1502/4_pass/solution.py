import json

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }
    
    # Define fixed events
    fixed_events = [
        {'city': 'Madrid', 'day_range': (6, 7)},
        {'city': 'Vienna', 'day_range': (3, 6)},
        {'city': 'Riga', 'day_range': (20, 23)},
        {'city': 'Tallinn', 'day_range': (23, 27)},
        {'city': 'Krakow', 'day_range': (11, 15)}
    ]
    
    # Initialize itinerary with fixed events
    itinerary = []
    for event in fixed_events:
        start, end = event['day_range']
        itinerary.append({
            'day_range': f'Day {start}-{end}',
            'place': event['city']
        })
    
    # Calculate remaining days needed for each city
    remaining_days = {}
    for city, days in cities.items():
        allocated = 0
        for event in fixed_events:
            if event['city'] == city:
                start, end = event['day_range']
                allocated += (end - start + 1)
        remaining = days - allocated
        if remaining > 0:
            remaining_days[city] = remaining
    
    # Assign remaining days to cities, ensuring flight connections
    current_day = 1
    last_city = None
    
    # We'll process cities in a specific order that makes sense with the fixed events
    # Bucharest (3 days) before Vienna (fixed 3-6)
    if 'Bucharest' in remaining_days:
        end_day = current_day + remaining_days['Bucharest'] - 1
        itinerary.append({
            'day_range': f'Day {current_day}-{end_day}',
            'place': 'Bucharest'
        })
        current_day = end_day + 1
        last_city = 'Bucharest'
    
    # Vienna is already covered by fixed event
    
    # After Vienna (ends day 6), Madrid is fixed on day 6-7
    # Then we can go to Seville (connected to Madrid)
    if 'Seville' in remaining_days:
        start_day = max(current_day, 8)  # After Madrid
        end_day = start_day + remaining_days['Seville'] - 1
        itinerary.append({
            'day_range': f'Day {start_day}-{end_day}',
            'place': 'Seville'
        })
        current_day = end_day + 1
        last_city = 'Seville'
    
    # Then Valencia (connected to Seville)
    if 'Valencia' in remaining_days:
        end_day = current_day + remaining_days['Valencia'] - 1
        itinerary.append({
            'day_range': f'Day {current_day}-{end_day}',
            'place': 'Valencia'
        })
        current_day = end_day + 1
        last_city = 'Valencia'
    
    # Krakow is already covered by fixed event
    
    # After Krakow (ends day 15), we can go to Frankfurt (connected to Krakow)
    if 'Frankfurt' in remaining_days:
        start_day = max(current_day, 16)  # After Krakow
        end_day = start_day + remaining_days['Frankfurt'] - 1
        itinerary.append({
            'day_range': f'Day {start_day}-{end_day}',
            'place': 'Frankfurt'
        })
        current_day = end_day + 1
        last_city = 'Frankfurt'
    
    # Riga is already covered by fixed event
    
    # Tallinn is already covered by fixed event
    
    # Santorini can be visited from Frankfurt or Madrid
    if 'Santorini' in remaining_days:
        # Find a gap between day 1-27 that's not occupied
        # We'll place it after Frankfurt but before Riga
        start_day = 19  # After Frankfurt, before Riga
        end_day = start_day + remaining_days['Santorini'] - 1
        if end_day >= 20:  # Don't overlap with Riga
            start_day = 16  # Try earlier
            end_day = start_day + remaining_days['Santorini'] - 1
        itinerary.append({
            'day_range': f'Day {start_day}-{end_day}',
            'place': 'Santorini'
        })
    
    # Validate all cities are covered
    visited_cities = {e['place'] for e in itinerary}
    missing = set(cities.keys()) - visited_cities
    if missing:
        return {'error': f'Missing cities: {missing}'}
    
    # Check day overlaps and total days
    day_usage = [0] * 28  # 1-based index for days 1-27
    try:
        for entry in itinerary:
            parts = entry['day_range'].split('-')
            start = int(parts[0].split(' ')[1])
            end = int(parts[1])
            for day in range(start, end + 1):
                if day_usage[day] == 1:
                    return {'error': f'Day {day} is double-booked'}
                day_usage[day] = 1
        
        if sum(day_usage) != 27:
            return {'error': f'Total days used is {sum(day_usage)}, should be 27'}
    except Exception as e:
        return {'error': f'Error validating itinerary: {str(e)}'}
    
    # Sort itinerary by day range
    def get_day_start(entry):
        parts = entry['day_range'].split('-')
        return int(parts[0].split(' ')[1])
    
    itinerary_sorted = sorted(itinerary, key=get_day_start)
    
    return {'itinerary': itinerary_sorted}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))