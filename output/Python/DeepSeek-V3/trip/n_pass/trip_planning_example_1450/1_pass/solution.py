import json
from itertools import permutations

def main():
    # Define city stay durations
    city_durations = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    # Define fixed events
    fixed_events = [
        {'city': 'Istanbul', 'day_range': (25, 29)},
        {'city': 'Krakow', 'day_range': (5, 9)}
    ]
    
    # Define direct flights
    direct_flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Frankfurt', 'Hamburg', 'Munich'],
        'Stockholm': ['Oslo', 'Munich', 'Hamburg', 'Istanbul', 'Santorini', 'Krakow', 'Frankfurt'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Oslo', 'Munich', 'Stockholm'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence', 'Krakow', 'Vilnius'],
        'Hamburg': ['Stockholm', 'Munich', 'Istanbul', 'Frankfurt', 'Oslo'],
        'Vilnius': ['Istanbul', 'Frankfurt', 'Oslo', 'Munich', 'Krakow'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Oslo', 'Stockholm', 'Florence', 'Munich', 'Hamburg', 'Vilnius'],
        'Florence': ['Frankfurt', 'Munich'],
        'Istanbul': ['Krakow', 'Oslo', 'Stockholm', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg'],
        'Santorini': ['Stockholm', 'Oslo']
    }
    
    # Generate all possible city orders
    cities = list(city_durations.keys())
    possible_orders = permutations(cities)
    
    # Find a valid itinerary
    valid_itinerary = None
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        # Check fixed events first
        for event in fixed_events:
            if event['city'] not in order:
                valid = False
                break
        
        if not valid:
            continue
        
        # Build itinerary
        for city in order:
            # Check if we need to move to this city
            if prev_city is not None and city != prev_city:
                # Check if there's a direct flight
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                # Transition day (counts for both cities)
                itinerary.append({
                    'day_range': f"Day {current_day}",
                    'place': f"{prev_city} to {city}"
                })
                current_day += 0  # Transition day counts for both
            
            # Add stay duration
            duration = city_durations[city]
            
            # Check fixed events
            for event in fixed_events:
                if event['city'] == city:
                    start, end = event['day_range']
                    required_days = end - start + 1
                    if duration < required_days:
                        valid = False
                        break
                    # Ensure the stay covers the event
                    if not (start <= current_day <= end or 
                            start <= current_day + duration - 1 <= end or
                            (current_day <= start and current_day + duration - 1 >= end)):
                        valid = False
                        break
            
            if not valid:
                break
            
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + duration - 1}",
                'place': city
            })
            current_day += duration
            prev_city = city
        
        # Check total days
        if valid and current_day - 1 <= 32:
            valid_itinerary = itinerary
            break
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    if not valid_itinerary:
        valid_itinerary = [{'day_range': 'Day 1-32', 'place': 'No valid itinerary found'}]
    
    # Output as JSON
    print(json.dumps({'itinerary': valid_itinerary}))

if __name__ == "__main__":
    main()