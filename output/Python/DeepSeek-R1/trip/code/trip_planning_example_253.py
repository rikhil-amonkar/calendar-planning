import json

def calculate_itinerary():
    cities = {
        'Vienna': 7,
        'Lyon': 3,
        'Amsterdam': 3,
        'Santorini': 4
    }
    
    fixed_events = {
        'Lyon': {'start': 7, 'end': 9},
        'Amsterdam': {'start': 9, 'end': 11}
    }
    
    itinerary = []
    
    # Vienna: before Lyon, 7 days
    vienna_end = fixed_events['Lyon']['start']  # Fly to Lyon on day7
    itinerary.append({'day_range': f'Day 1-{vienna_end}', 'place': 'Vienna'})
    
    # Lyon: fixed days 7-9
    lyon_start = fixed_events['Lyon']['start']
    lyon_end = fixed_events['Lyon']['end']
    itinerary.append({'day_range': f'Day {lyon_start}-{lyon_end}', 'place': 'Lyon'})
    
    # Amsterdam: fixed days 9-11
    ams_start = fixed_events['Amsterdam']['start']
    ams_end = fixed_events['Amsterdam']['end']
    itinerary.append({'day_range': f'Day {ams_start}-{ams_end}', 'place': 'Amsterdam'})
    
    # Santorini: remaining days after Amsterdam
    santorini_start = ams_end  # Fly on day11
    santorini_end = 14
    itinerary.append({'day_range': f'Day {santorini_start}-{santorini_end}', 'place': 'Santorini'})
    
    return {'itinerary': itinerary}

print(json.dumps(calculate_itinerary(), indent=None))