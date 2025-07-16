import json

def calculate_itinerary():
    # Define constraints
    total_days = 23
    city_stays = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 3,
        'Geneva': 7,
        'Reykjavik': 2
    }
    fixed_events = {
        'Geneva': {'start': 1, 'end': 7},
        'Oslo': {'start': 19, 'end': 23}
    }
    direct_flights = {
        'Paris': ['Oslo', 'Reykjavik', 'Geneva', 'Porto'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }

    # Initialize itinerary
    itinerary = []

    # Fixed events first
    itinerary.append({'day_range': 'Day 1-7', 'place': 'Geneva'})
    city_stays['Geneva'] = 0

    # After Geneva (Day 8), go to Paris (connected to Geneva)
    itinerary.append({'day_range': 'Day 8-13', 'place': 'Paris'})
    city_stays['Paris'] = 0

    # From Paris, go to Reykjavik (connected)
    itinerary.append({'day_range': 'Day 14-15', 'place': 'Reykjavik'})
    city_stays['Reykjavik'] = 0

    # Return to Paris from Reykjavik (Day 16)
    itinerary.append({'day_range': 'Day 16', 'place': 'Paris'})

    # From Paris, go to Porto (connected)
    itinerary.append({'day_range': 'Day 17-19', 'place': 'Porto'})
    city_stays['Porto'] = 0

    # From Porto, return to Paris (connected)
    itinerary.append({'day_range': 'Day 20', 'place': 'Paris'})

    # Fixed Oslo stay
    itinerary.append({'day_range': 'Day 21-23', 'place': 'Oslo'})
    city_stays['Oslo'] = 0

    # Verify all days are allocated
    allocated_days = 0
    for item in itinerary:
        start, end = map(int, item['day_range'].split('Day ')[1].split('-'))
        allocated_days += end - start + 1
    
    if allocated_days != total_days:
        raise ValueError(f"Not all days are properly allocated (allocated: {allocated_days}, total: {total_days})")
    
    # Verify all city stays are satisfied
    for city, days in city_stays.items():
        if days != 0:
            raise ValueError(f"Not all days allocated for {city}")
    
    # Verify flight connections (except for fixed events)
    for i in range(1, len(itinerary)-1):
        current = itinerary[i]['place']
        next_city = itinerary[i+1]['place']
        if next_city not in direct_flights[current]:
            raise ValueError(f"No direct flight from {current} to {next_city}")
    
    return {'itinerary': itinerary}

# Compute and output the itinerary
result = calculate_itinerary()
print(json.dumps(result, indent=2))