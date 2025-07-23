import json

def find_itinerary():
    # Define constraints
    total_days = 8
    city_stays = {
        'Prague': 4,
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Florence': 2
    }
    
    # Direct flights (undirected graph)
    direct_flights = {
        'Stuttgart': ['Split', 'Krakow'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Prague': ['Split', 'Florence', 'Krakow'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Florence': ['Prague'],
        'Florence': ['Prague']
    }
    
    # Correct flight connections (handling both spellings)
    flight_connections = {
        'Stuttgart': ['Split', 'Krakow'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Prague': ['Split', 'Florence', 'Krakow'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Florence': ['Prague']
    }
    
    # Event constraints
    wedding_in_stuttgart = (2, 3)  # Must be in Stuttgart on day 2 or 3
    friends_in_split = (3, 4)      # Must be in Split on day 3 or 4
    
    # We'll use a more targeted approach rather than brute-force permutations
    
    # Possible valid sequences based on flight connections
    possible_sequences = [
        ['Stuttgart', 'Split', 'Prague', 'Florence', 'Krakow'],
        ['Stuttgart', 'Split', 'Krakow', 'Prague', 'Florence'],
        ['Stuttgart', 'Krakow', 'Split', 'Prague', 'Florence'],
        ['Stuttgart', 'Krakow', 'Prague', 'Split', 'Florence'],
        ['Stuttgart', 'Krakow', 'Prague', 'Florence', 'Split']
    ]
    
    for city_order in possible_sequences:
        # Assign days to cities in this order
        itinerary_days = []
        current_day = 1
        
        for city in city_order:
            if city not in city_stays:
                continue  # Skip if city name is invalid
            
            stay_days = city_stays[city]
            end_day = current_day + stay_days - 1
            if end_day > total_days:
                break
            
            itinerary_days.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            current_day = end_day + 1
        
        if current_day != total_days + 1:
            continue  # Doesn't use all days exactly
        
        # Check event constraints
        wedding_ok = False
        split_ok = False
        
        for entry in itinerary_days:
            day_range = entry['day_range']
            place = entry['place']
            start_day = int(day_range.split('-')[0].split(' ')[1])
            end_day = int(day_range.split('-')[1])
            
            # Check wedding in Stuttgart on day 2 or 3
            if place == 'Stuttgart':
                if start_day <= wedding_in_stuttgart[1] and end_day >= wedding_in_stuttgart[0]:
                    wedding_ok = True
            
            # Check friends in Split on day 3 or 4
            if place == 'Split':
                if start_day <= friends_in_split[1] and end_day >= friends_in_split[0]:
                    split_ok = True
        
        if wedding_ok and split_ok:
            return {'itinerary': itinerary_days}
    
    return {'itinerary': []}  # No valid itinerary found

# Run the function and print the result as JSON
result = find_itinerary()
print(json.dumps(result, indent=2))