import json
from itertools import permutations

def main():
    # Define the constraints
    total_days = 17
    city_stays = {
        'Mykonos': 3,
        'Riga': 3,
        'Munich': 4,
        'Bucharest': 4,
        'Rome': 4,
        'Nice': 3,
        'Krakow': 2
    }
    
    # Define the flight connections (undirected)
    flights = {
        'Nice': ['Riga', 'Rome', 'Mykonos', 'Munich'],
        'Riga': ['Nice', 'Bucharest', 'Rome', 'Munich'],
        'Bucharest': ['Riga', 'Munich', 'Rome'],
        'Munich': ['Bucharest', 'Mykonos', 'Rome', 'Nice', 'Riga', 'Krakow'],
        'Mykonos': ['Munich', 'Nice', 'Rome'],
        'Rome': ['Nice', 'Munich', 'Mykonos', 'Bucharest', 'Riga'],
        'Krakow': ['Munich']
    }
    
    # Fixed events that must be included
    fixed_events = [
        {'place': 'Rome', 'day_range': (1, 4)},  # Days 1-4
        {'place': 'Mykonos', 'day_range': (5, 7)},  # Days 5-7 (after Rome)
        {'place': 'Krakow', 'day_range': (16, 17)}  # Days 16-17
    ]
    
    # Remove fixed cities from permutations since their positions are known
    flexible_cities = [city for city in city_stays.keys() 
                      if city not in ['Rome', 'Mykonos', 'Krakow']]
    
    # Calculate remaining days between fixed events
    # Days 8-15 (8 days total) between Mykonos (ends day 7) and Krakow (starts day 16)
    remaining_days = 15 - 7  # Days 8-15 (8 days total)
    
    # We'll try all permutations of the flexible cities
    for perm in permutations(flexible_cities):
        # Check if the permutation fits the remaining days
        total_flexible_stays = sum(city_stays[city] for city in perm)
        if total_flexible_stays != remaining_days:
            continue
        
        # Check flight connections between cities
        valid = True
        prev_city = 'Mykonos'  # Last city before flexible sequence
        
        # Build the flexible part of the itinerary
        flexible_itinerary = []
        current_day = 8  # Start after Mykonos (day 7)
        
        for city in perm:
            # Check flight connection
            if city not in flights[prev_city]:
                valid = False
                break
            
            stay = city_stays[city]
            end_day = current_day + stay - 1
            
            flexible_itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            
            prev_city = city
            current_day = end_day + 1
        
        if not valid:
            continue
        
        # Check connection to Krakow
        if 'Krakow' not in flights[prev_city]:
            continue
        
        # Check if we end at day 15 (since Krakow is 16-17)
        if current_day != 16:
            continue
        
        # Combine all parts of the itinerary
        full_itinerary = [
            {'day_range': "Day 1-4", 'place': 'Rome'},
            {'day_range': "Day 5-7", 'place': 'Mykonos'}
        ]
        full_itinerary.extend(flexible_itinerary)
        full_itinerary.append({'day_range': "Day 16-17", 'place': 'Krakow'})
        
        # Verify all cities are visited with correct durations
        visited_cities = {item['place'] for item in full_itinerary}
        if visited_cities != set(city_stays.keys()):
            continue
        
        # Verify all day ranges are correct and cover all days
        day_set = set()
        for item in full_itinerary:
            start, end = map(int, item['day_range'].split(' ')[1].split('-'))
            day_set.update(range(start, end+1))
        
        if day_set != set(range(1, 18)):
            continue
        
        # Found valid itinerary
        print(json.dumps({'itinerary': full_itinerary}, indent=2))
        return
    
    # If no valid itinerary found
    print(json.dumps({'itinerary': []}, indent=2))

if __name__ == "__main__":
    main()