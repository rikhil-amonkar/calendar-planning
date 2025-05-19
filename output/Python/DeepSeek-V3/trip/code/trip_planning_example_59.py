import json

def plan_trip():
    total_days = 16
    lyon_days = 7
    bucharest_days = 7
    porto_days = 4
    wedding_in_bucharest_range = (1, 7)
    
    # Calculate remaining days (should be zero if inputs are correct)
    remaining_days = total_days - (lyon_days + bucharest_days + porto_days)
    if remaining_days != 0:
        raise ValueError("The total days don't match the sum of days in each city.")
    
    # Determine the order based on flight connections and wedding constraint
    # Possible connections: Bucharest <-> Lyon <-> Porto
    # Wedding must happen in Bucharest between day 1-7, so Bucharest must be first or include day 1-7
    
    # Option 1: Start in Bucharest
    itinerary = []
    current_day = 1
    
    # Stay in Bucharest for wedding (must include days 1-7)
    bucharest_start = current_day
    bucharest_end = bucharest_start + bucharest_days - 1
    itinerary.append({
        'day_range': f'Day {bucharest_start}-{bucharest_end}',
        'place': 'Bucharest'
    })
    current_day = bucharest_end + 1
    
    # Fly to Lyon (direct flight exists)
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': 'Bucharest',
        'to': 'Lyon'
    })
    
    # Stay in Lyon
    lyon_start = current_day + 1
    lyon_end = lyon_start + lyon_days - 1
    itinerary.append({
        'day_range': f'Day {lyon_start}-{lyon_end}',
        'place': 'Lyon'
    })
    current_day = lyon_end + 1
    
    # Fly to Porto (direct flight exists)
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': 'Lyon',
        'to': 'Porto'
    })
    
    # Stay in Porto
    porto_start = current_day + 1
    porto_end = porto_start + porto_days - 1
    itinerary.append({
        'day_range': f'Day {porto_start}-{porto_end}',
        'place': 'Porto'
    })
    
    # Verify all days are accounted for
    if porto_end != total_days:
        raise ValueError("The itinerary doesn't cover all days.")
    
    return itinerary

if __name__ == "__main__":
    itinerary = plan_trip()
    print(json.dumps(itinerary, indent=2))