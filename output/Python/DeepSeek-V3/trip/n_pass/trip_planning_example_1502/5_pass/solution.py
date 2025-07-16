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
    
    # Define fixed events (adjusted to avoid overlaps)
    fixed_events = [
        {'city': 'Madrid', 'day_range': (7, 8)},  # Changed to days 7-8 to avoid overlap with Vienna
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
                allocated += (end - start)
        remaining = days - allocated
        if remaining > 0:
            remaining_days[city] = remaining
    
    # Assign remaining days to cities, ensuring flight connections
    current_day = 1
    
    # Bucharest first (3 days)
    if 'Bucharest' in remaining_days:
        end_day = current_day + remaining_days['Bucharest'] - 1
        itinerary.append({
            'day_range': f'Day {current_day}-{end_day}',
            'place': 'Bucharest'
        })
        current_day = end_day + 1
    
    # Vienna is fixed days 3-6
    
    # Madrid is now days 7-8 (was adjusted to avoid overlap)
    
    # Seville after Madrid (days 9-10)
    if 'Seville' in remaining_days:
        end_day = 8 + remaining_days['Seville']
        itinerary.append({
            'day_range': f'Day 9-{end_day}',
            'place': 'Seville'
        })
        current_day = end_day + 1
    
    # Valencia after Seville (days 11-14)
    # But Krakow is fixed 11-15, so we need to adjust
    if 'Valencia' in remaining_days:
        # Place Valencia before Krakow if possible
        # Days 9-12 (but Seville is 9-10)
        end_day = 10 + remaining_days['Valencia']
        if end_day <= 10:  # Doesn't overlap with Krakow
            itinerary.append({
                'day_range': f'Day 9-{end_day}',
                'place': 'Valencia'
            })
        else:
            # Place after Krakow
            end_day = 15 + remaining_days['Valencia']
            itinerary.append({
                'day_range': f'Day 16-{end_day}',
                'place': 'Valencia'
            })
        current_day = end_day + 1
    
    # Krakow is fixed 11-15
    
    # Frankfurt after Krakow (days 16-19)
    if 'Frankfurt' in remaining_days:
        end_day = 15 + remaining_days['Frankfurt']
        itinerary.append({
            'day_range': f'Day 16-{end_day}',
            'place': 'Frankfurt'
        })
        current_day = end_day + 1
    
    # Riga is fixed 20-23
    
    # Tallinn is fixed 23-27
    
    # Santorini needs 3 days - place before Riga (days 17-19)
    if 'Santorini' in remaining_days:
        # Find available days between Frankfurt and Riga
        start_day = 20 - remaining_days['Santorini']
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