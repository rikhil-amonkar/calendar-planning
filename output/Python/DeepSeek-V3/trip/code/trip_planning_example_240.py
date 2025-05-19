import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    cities = {
        'Prague': {'days': 2},
        'Berlin': {'days': 3, 'conference_days': [6, 8]},
        'Tallinn': {'days': 5, 'relatives_days': (8, 12)},
        'Stockholm': {'days': 5}
    }
    
    direct_flights = {
        'Berlin': ['Tallinn', 'Stockholm'],
        'Tallinn': ['Berlin', 'Prague', 'Stockholm'],
        'Stockholm': ['Tallinn', 'Prague', 'Berlin'],
        'Prague': ['Tallinn', 'Stockholm']
    }
    
    # Initialize itinerary
    itinerary = []
    current_day = 1
    current_city = None
    remaining_cities = cities.copy()
    
    # Determine the starting city
    # Must be in Berlin on day 6, so start before that
    # Possible starting cities: Prague, Stockholm, Tallinn
    possible_starters = ['Prague', 'Stockholm', 'Tallinn']
    starter = None
    
    for city in possible_starters:
        if city != 'Berlin':
            starter = city
            break
    
    current_city = starter
    stay_duration = cities[starter]['days']
    end_day = current_day + stay_duration - 1
    
    # Add first stay
    itinerary.append({
        'day_range': f'Day {current_day}-{end_day}',
        'place': current_city
    })
    
    current_day = end_day + 1
    del remaining_cities[current_city]
    
    # Next, must be in Berlin by day 6
    # Current day is after first stay, check if we need to go to Berlin immediately
    if current_day <= 6:
        # Need to be in Berlin by day 6
        next_city = 'Berlin'
        # Check if there's a direct flight
        if next_city in direct_flights[current_city]:
            # Add flight
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': current_city,
                'to': next_city
            })
            current_city = next_city
            # Determine stay duration in Berlin
            # Must cover day 6 and day 8
            # Stay until at least day 8
            stay_duration = (8 - current_day) + 1
            end_day = current_day + stay_duration - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': current_city
            })
            current_day = end_day + 1
            del remaining_cities[current_city]
    
    # After Berlin, must go to Tallinn for relatives between day 8 and 12
    if current_day <= 8 and 'Tallinn' in remaining_cities:
        next_city = 'Tallinn'
        if next_city in direct_flights[current_city]:
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': current_city,
                'to': next_city
            })
            current_city = next_city
            # Stay in Tallinn until day 12
            stay_duration = 12 - current_day + 1
            end_day = current_day + stay_duration - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': current_city
            })
            current_day = end_day + 1
            del remaining_cities[current_city]
    
    # Check if all days are accounted for
    if current_day <= total_days:
        # Visit remaining cities if any
        for city in remaining_cities:
            if city != current_city and city in direct_flights[current_city]:
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': current_city,
                    'to': city
                })
                current_city = city
                stay_duration = remaining_cities[city]['days']
                end_day = current_day + stay_duration - 1
                if end_day > total_days:
                    stay_duration = total_days - current_day + 1
                    end_day = current_day + stay_duration - 1
                itinerary.append({
                    'day_range': f'Day {current_day}-{end_day}',
                    'place': current_city
                })
                current_day = end_day + 1
                del remaining_cities[city]
                break
    
    return itinerary

itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))