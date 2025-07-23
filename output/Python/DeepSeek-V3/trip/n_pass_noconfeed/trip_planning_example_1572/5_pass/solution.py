import json
from itertools import permutations

def main():
    # Define the cities and their required days (sums to 30)
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
        'Naples': 2
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
    
    # Fixed events with their day ranges
    fixed_events = [
        {'place': 'Berlin', 'day_range': (1, 2)},    # Days 1-2
        {'place': 'Nice', 'day_range': (12, 13)},    # Days 12-13
        {'place': 'Stockholm', 'day_range': (20, 22)} # Days 20-22
    ]
    
    # Initialize itinerary with fixed events
    itinerary = [
        {'day_range': 'Day 1-2', 'place': 'Berlin'},
        {'day_range': 'Day 12-13', 'place': 'Nice'},
        {'day_range': 'Day 20-22', 'place': 'Stockholm'}
    ]
    
    # Remaining cities and days (excluding fixed events)
    remaining_cities = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Zurich': 5,
        'Seville': 3,
        'Milan': 3,
        'Naples': 2
    }
    
    # Available time slots between fixed events
    time_slots = [
        {'start': 3, 'end': 11},    # Between Berlin and Nice
        {'start': 14, 'end': 19}    # Between Nice and Stockholm
    ]
    
    # We'll use a more flexible approach than permutations
    remaining_city_list = list(remaining_cities.keys())
    max_attempts = 10000
    attempts = 0
    
    for _ in range(max_attempts):
        attempts += 1
        # Shuffle the remaining cities
        import random
        random.shuffle(remaining_city_list)
        
        # Try to place cities in the available time slots
        current_itinerary = []
        current_day = 3  # Start after Berlin
        
        valid_placement = True
        for city in remaining_city_list:
            days_needed = remaining_cities[city]
            
            # Find next available slot
            placed = False
            for slot in time_slots:
                if current_day >= slot['start'] and current_day + days_needed - 1 <= slot['end']:
                    current_itinerary.append({
                        'day_range': f'Day {current_day}-{current_day + days_needed - 1}',
                        'place': city
                    })
                    current_day += days_needed
                    placed = True
                    break
            
            if not placed:
                valid_placement = False
                break
        
        if not valid_placement:
            continue
        
        # Check flight connections
        flight_path = ['Berlin']  # Start in Berlin
        
        # Get the order of cities from the itinerary
        itinerary_order = []
        for item in current_itinerary + [{'day_range': 'Day 20-22', 'place': 'Stockholm'}]:
            if item['place'] not in itinerary_order:
                itinerary_order.append(item['place'])
        
        valid_flights = True
        for i in range(len(itinerary_order) - 1):
            current = itinerary_order[i]
            next_city = itinerary_order[i+1]
            if next_city not in direct_flights.get(current, []):
                valid_flights = False
                break
        
        if valid_flights:
            # Combine all parts
            final_itinerary = [
                {'day_range': 'Day 1-2', 'place': 'Berlin'}
            ]
            final_itinerary.extend(current_itinerary)
            final_itinerary.append({'day_range': 'Day 12-13', 'place': 'Nice'})
            final_itinerary.append({'day_range': 'Day 20-22', 'place': 'Stockholm'})
            
            # Sort by day range
            def get_start_day(item):
                return int(item['day_range'].split('-')[0].split(' ')[1])
            
            final_itinerary.sort(key=get_start_day)
            
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