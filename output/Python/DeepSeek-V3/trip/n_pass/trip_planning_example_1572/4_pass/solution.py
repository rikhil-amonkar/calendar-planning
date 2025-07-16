import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
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
    
    # Direct flights
    direct_flights = {
        'Paris': ['Stockholm', 'Seville', 'Zurich', 'Nice', 'Lyon', 'Riga', 'Naples', 'Milan'],
        'Stockholm': ['Paris', 'Riga', 'Berlin', 'Zurich', 'Nice', 'Milan'],
        'Seville': ['Paris', 'Milan'],
        'Naples': ['Zurich', 'Milan', 'Paris', 'Berlin', 'Nice'],
        'Nice': ['Riga', 'Paris', 'Zurich', 'Stockholm', 'Naples', 'Lyon', 'Berlin'],
        'Riga': ['Nice', 'Milan', 'Paris', 'Stockholm', 'Zurich', 'Berlin'],
        'Berlin': ['Milan', 'Stockholm', 'Naples', 'Zurich', 'Riga', 'Paris', 'Nice'],
        'Milan': ['Berlin', 'Paris', 'Riga', 'Naples', 'Zurich', 'Stockholm', 'Seville'],
        'Zurich': ['Naples', 'Paris', 'Nice', 'Stockholm', 'Riga', 'Milan', 'Berlin'],
        'Lyon': ['Paris', 'Nice']
    }
    
    # Fixed events
    fixed_events = [
        {'place': 'Berlin', 'day_range': (1, 2)},
        {'place': 'Stockholm', 'day_range': (20, 22)},
        {'place': 'Nice', 'day_range': (12, 13)}
    ]
    
    # Calculate used days by fixed events
    fixed_days = 0
    for event in fixed_events:
        start, end = event['day_range']
        fixed_days += end - start + 1
    
    # Remaining cities to schedule
    remaining_cities = [city for city in city_days.keys() 
                       if city not in {e['place'] for e in fixed_events}]
    
    # Check if remaining days match required days
    required_days = sum(city_days[city] for city in remaining_cities)
    if required_days != 23 - fixed_days:
        return {'itinerary': []}
    
    # Available time slots (between fixed events)
    available_slots = [
        (3, 11),   # After Berlin, before Nice
        (14, 19)   # After Nice, before Stockholm
    ]
    
    # Generate all possible permutations of remaining cities
    for perm in permutations(remaining_cities):
        itinerary = []
        current_slot = 0
        current_day = available_slots[current_slot][0]
        valid = True
        
        # Add fixed events to itinerary first
        for event in fixed_events:
            start, end = event['day_range']
            itinerary.append({
                'day_range': f'Day {start}-{end}',
                'place': event['place']
            })
        
        # Try to schedule remaining cities
        temp_schedule = []
        for city in perm:
            days_needed = city_days[city]
            
            # Check if fits in current slot
            if current_day + days_needed - 1 <= available_slots[current_slot][1]:
                end_day = current_day + days_needed - 1
                temp_schedule.append({
                    'day_range': f'Day {current_day}-{end_day}',
                    'place': city
                })
                current_day = end_day + 1
            else:
                # Move to next slot
                current_slot += 1
                if current_slot >= len(available_slots):
                    valid = False
                    break
                current_day = available_slots[current_slot][0]
                
                # Try again in new slot
                if current_day + days_needed - 1 <= available_slots[current_slot][1]:
                    end_day = current_day + days_needed - 1
                    temp_schedule.append({
                        'day_range': f'Day {current_day}-{end_day}',
                        'place': city
                    })
                    current_day = end_day + 1
                else:
                    valid = False
                    break
        
        if not valid:
            continue
        
        # Combine and sort the itinerary
        full_itinerary = itinerary + temp_schedule
        full_itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
        
        # Verify flight connections
        flight_valid = True
        for i in range(len(full_itinerary) - 1):
            current = full_itinerary[i]['place']
            next_city = full_itinerary[i+1]['place']
            current_end = int(full_itinerary[i]['day_range'].split('-')[1])
            next_start = int(full_itinerary[i+1]['day_range'].split('-')[0].split(' ')[1])
            
            # Check if consecutive and need flight
            if next_start == current_end + 1:
                if next_city not in direct_flights.get(current, []):
                    flight_valid = False
                    break
        
        if flight_valid:
            return {'itinerary': full_itinerary}
    
    return {'itinerary': []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))