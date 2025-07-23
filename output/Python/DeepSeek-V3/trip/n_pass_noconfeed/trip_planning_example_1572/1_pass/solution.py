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
    
    # Fixed events
    fixed_events = [
        {'place': 'Berlin', 'day_range': (1, 2)},
        {'place': 'Nice', 'day_range': (12, 13)},
        {'place': 'Stockholm', 'day_range': (20, 22)}
    ]
    
    # Initialize the itinerary with fixed events
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
    total_remaining_days = 23 - sum(fixed_cities.values())
    
    # Check if remaining days match
    if sum(remaining_cities.values()) != total_remaining_days:
        print(json.dumps({"error": "Total days do not match"}, indent=2))
        return
    
    # Generate possible orders for remaining cities
    remaining_city_list = list(remaining_cities.keys())
    
    # Try all permutations (not optimal for large n, but manageable for small n)
    for perm in permutations(remaining_city_list):
        current_itinerary = []
        valid = True
        
        # Check if the permutation can be connected via direct flights
        for i in range(len(perm) - 1):
            if perm[i+1] not in direct_flights.get(perm[i], []):
                valid = False
                break
        
        if not valid:
            continue
        
        # Check if the permutation can fit into the remaining days
        day = 3  # Start after Berlin (days 1-2)
        for city in perm:
            days_needed = remaining_cities[city]
            current_itinerary.append({'day_range': f'Day {day}-{day + days_needed - 1}', 'place': city})
            day += days_needed
        
        # Check if the last day is before day 20 (Stockholm event)
        if day <= 20:
            # Insert the Stockholm event
            final_itinerary = []
            for entry in current_itinerary:
                final_itinerary.append(entry)
            
            # Add the fixed events
            final_itinerary.insert(0, {'day_range': 'Day 1-2', 'place': 'Berlin'})
            final_itinerary.append({'day_range': 'Day 20-22', 'place': 'Stockholm'})
            
            # Check Nice event
            nice_found = False
            for entry in final_itinerary:
                if entry['place'] == 'Nice':
                    start_day = int(entry['day_range'].split('-')[0].split(' ')[1])
                    end_day = int(entry['day_range'].split('-')[1])
                    if start_day <= 12 and end_day >= 13:
                        nice_found = True
                        break
            
            if not nice_found:
                continue
            
            # Output the valid itinerary
            print(json.dumps({"itinerary": final_itinerary}, indent=2))
            return
    
    # If no valid itinerary found
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()