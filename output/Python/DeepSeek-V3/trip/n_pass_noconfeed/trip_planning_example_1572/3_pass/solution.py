import json
from itertools import permutations

def main():
    # Define the cities and their required days
    city_days = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Berlin': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    
    # Define the direct flights as a graph
    direct_flights = {
        'Paris': ['Stockholm', 'Seville', 'Zurich', 'Nice', 'Lyon', 'Riga', 'Naples', 'Milan'],
        'Seville': ['Paris', 'Milan'],
        'Naples': ['Zurich', 'Milan', 'Berlin', 'Paris', 'Nice'],
        'Nice': ['Riga', 'Paris', 'Zurich', 'Stockholm', 'Naples', 'Lyon', 'Berlin'],
        'Berlin': ['Milan', 'Stockholm', 'Naples', 'Zurich', 'Riga', 'Paris', 'Nice'],
        'Stockholm': ['Paris', 'Berlin', 'Riga', 'Zurich', 'Nice', 'Milan'],
        'Zurich': ['Naples', 'Paris', 'Nice', 'Stockholm', 'Riga', 'Milan', 'Berlin'],
        'Lyon': ['Paris', 'Nice'],
        'Riga': ['Nice', 'Paris', 'Milan', 'Stockholm', 'Zurich', 'Berlin'],
        'Milan': ['Berlin', 'Paris', 'Naples', 'Riga', 'Zurich', 'Stockholm', 'Seville']
    }
    
    # Fixed events with corrected day ranges
    fixed_events = [
        {'place': 'Berlin', 'day_range': (1, 2)},  # 2 days
        {'place': 'Nice', 'day_range': (12, 13)},  # 2 days
        {'place': 'Stockholm', 'day_range': (20, 22)}  # 3 days
    ]
    
    # Calculate total required days (should be 30)
    total_days = sum(city_days.values())
    if total_days != 30:
        print(json.dumps({"error": f"Total days should be 30, but got {total_days}"}, indent=2))
        return
    
    # Initialize itinerary with fixed events
    itinerary = []
    for event in fixed_events:
        start, end = event['day_range']
        itinerary.append({'day_range': f'Day {start}-{end}', 'place': event['place']})
    
    # Extract fixed cities and their days
    fixed_cities = {
        'Berlin': 2,
        'Nice': 2,
        'Stockholm': 3
    }
    
    # Remaining cities and days
    remaining_cities = {city: days for city, days in city_days.items() if city not in fixed_cities}
    total_remaining_days = sum(remaining_cities.values())
    
    if total_remaining_days != 23:  # 30 total - 7 fixed
        print(json.dumps({"error": f"Remaining days should be 23, but got {total_remaining_days}"}, indent=2))
        return
    
    # Generate possible orders for remaining cities (7 cities)
    remaining_city_list = list(remaining_cities.keys())
    
    # We'll try a limited number of permutations to avoid excessive computation
    max_attempts = 1000
    attempts = 0
    
    for perm in permutations(remaining_city_list):
        attempts += 1
        if attempts > max_attempts:
            break
            
        # Check flight connections
        valid_flights = True
        current_city = 'Berlin'  # Start from Berlin
        
        for next_city in perm:
            if next_city not in direct_flights.get(current_city, []):
                valid_flights = False
                break
            current_city = next_city
        
        # Check if we can fly to Stockholm from last city
        if valid_flights and 'Stockholm' not in direct_flights.get(current_city, []):
            valid_flights = False
        
        if not valid_flights:
            continue
        
        # Build itinerary
        day = 3  # Start after Berlin (days 1-2)
        current_itinerary = []
        valid_placement = True
        
        for city in perm:
            days_needed = remaining_cities[city]
            
            # Check if Nice is placed correctly (must include day 12-13)
            if city == 'Nice':
                if not (day <= 12 and day + days_needed - 1 >= 13):
                    valid_placement = False
                    break
            
            # Check if we have space before Stockholm (must end by day 19)
            if day + days_needed - 1 > 19:
                valid_placement = False
                break
                
            current_itinerary.append({'day_range': f'Day {day}-{day + days_needed - 1}', 'place': city})
            day += days_needed
            
        if not valid_placement:
            continue
            
        # Check if we have space for Stockholm (days 20-22)
        if day <= 20:
            # Combine all parts
            final_itinerary = [
                {'day_range': 'Day 1-2', 'place': 'Berlin'}
            ]
            final_itinerary.extend(current_itinerary)
            final_itinerary.append({'day_range': 'Day 20-22', 'place': 'Stockholm'})
            
            # Verify all cities are included
            included_cities = {item['place'] for item in final_itinerary}
            if included_cities == set(city_days.keys()):
                # Output the valid itinerary
                print(json.dumps({"itinerary": final_itinerary}, indent=2))
                return
    
    # If no valid itinerary found
    print(json.dumps({"error": "No valid itinerary found within reasonable attempts"}, indent=2))

if __name__ == "__main__":
    main()