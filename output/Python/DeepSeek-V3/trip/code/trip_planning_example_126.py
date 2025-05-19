import json

def calculate_itinerary():
    # Input parameters
    total_days = 11
    seville_days = 6
    paris_days = 2
    krakow_days = 5
    krakow_workshop_start = 1
    krakow_workshop_end = 5
    
    # Direct flight connections
    connections = {
        'Krakow': ['Paris'],
        'Paris': ['Krakow', 'Seville'],
        'Seville': ['Paris']
    }
    
    # Validate the days sum
    if (seville_days + paris_days + krakow_days) != total_days:
        raise ValueError("Total days in cities do not match the trip duration")
    
    # Determine the order of cities based on constraints
    # Workshop must be in Krakow between day 1-5, so start in Krakow
    itinerary = []
    current_day = 1
    
    # Stay in Krakow first (must be days 1-5)
    krakow_stay_end = current_day + krakow_days - 1
    itinerary.append({
        'day_range': f'Day {current_day}-{krakow_stay_end}',
        'place': 'Krakow'
    })
    current_day = krakow_stay_end + 1
    
    # Fly to Paris (only direct flight from Krakow)
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': 'Krakow',
        'to': 'Paris'
    })
    current_day += 1
    
    # Stay in Paris
    paris_stay_end = current_day + paris_days - 1
    itinerary.append({
        'day_range': f'Day {current_day}-{paris_stay_end}',
        'place': 'Paris'
    })
    current_day = paris_stay_end + 1
    
    # Fly to Seville (only direct flight from Paris)
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': 'Paris',
        'to': 'Seville'
    })
    current_day += 1
    
    # Stay in Seville
    seville_stay_end = current_day + seville_days - 1
    itinerary.append({
        'day_range': f'Day {current_day}-{seville_stay_end}',
        'place': 'Seville'
    })
    
    return itinerary

if __name__ == "__main__":
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))