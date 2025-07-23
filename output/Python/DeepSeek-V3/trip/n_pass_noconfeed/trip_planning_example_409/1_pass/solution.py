import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    city_days = {
        'Hamburg': 2,
        'Zurich': 3,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    
    # Direct flight connections
    connections = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Zurich', 'Helsinki', 'Bucharest', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Zurich', 1, 3),  # Wedding in Zurich between day 1 and day 3
        ('Split', 4, 10)    # Conference in Split between day 4 and day 10
    ]
    
    total_days = 12
    cities = list(city_days.keys())
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # Check if Zurich is visited between day 1-3 and Split between day 4-10
        valid = True
        itinerary = []
        current_day = 1
        
        # Check Zurich and Split constraints first
        zurich_pos = perm.index('Zurich')
        split_pos = perm.index('Split')
        
        # Zurich must be visited early enough to cover day 1-3
        # Split must be visited to cover day 4-10
        # This is a simplified check; actual day ranges are calculated later
        if zurich_pos > 2 or split_pos < 1:
            continue
        
        # Try to build itinerary
        temp_itinerary = []
        remaining_days = city_days.copy()
        prev_city = None
        
        for city in perm:
            if remaining_days[city] <= 0:
                continue
            
            # Determine stay duration
            stay_duration = remaining_days[city]
            
            # Check if current city is Zurich or Split to adjust stay based on constraints
            if city == 'Zurich':
                # Must cover day 1-3
                start_day = max(1, current_day)
                end_day = start_day + stay_duration - 1
                if not (start_day <= 3 and end_day >= 1):
                    valid = False
                    break
                # Adjust stay to fit the constraint
                if start_day > 1:
                    stay_duration = 3 - start_day + 1
                if end_day < 3:
                    stay_duration = 3 - start_day + 1
            
            elif city == 'Split':
                # Must cover day 4-10
                start_day = max(4, current_day)
                end_day = start_day + stay_duration - 1
                if not (start_day <= 10 and end_day >= 4):
                    valid = False
                    break
                # Ensure Split covers the conference days
                if start_day > 4:
                    stay_duration = min(stay_duration, 10 - start_day + 1)
                if end_day < 10:
                    stay_duration = min(stay_duration, 10 - start_day + 1)
            
            # Add to itinerary
            end_day = current_day + stay_duration - 1
            temp_itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            
            # Update remaining days
            remaining_days[city] -= stay_duration
            current_day = end_day + 1
            
            # Check if we've exceeded total days
            if current_day > total_days:
                valid = False
                break
            
            # Check if all days are allocated
            if all(v == 0 for v in remaining_days.values()):
                break
        
        # Check if all cities' days are satisfied and total days match
        if valid and current_day <= total_days + 1 and all(v == 0 for v in remaining_days.values()):
            # Verify Zurich and Split constraints
            zurich_covered = False
            split_covered = False
            for entry in temp_itinerary:
                if entry['place'] == 'Zurich':
                    start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                    if start <= 3 and end >= 1:
                        zurich_covered = True
                elif entry['place'] == 'Split':
                    start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                    if start <= 10 and end >= 4:
                        split_covered = True
            if zurich_covered and split_covered:
                itinerary = temp_itinerary
                break
    
    if not itinerary:
        return {"itinerary": []}
    
    # Post-process to merge consecutive stays in the same city (though unlikely here)
    merged_itinerary = []
    current_entry = itinerary[0]
    for entry in itinerary[1:]:
        if entry['place'] == current_entry['place']:
            # Merge
            start_current = int(current_entry['day_range'].split('Day ')[1].split('-')[0])
            end_current = int(current_entry['day_range'].split('-')[1])
            start_new = int(entry['day_range'].split('Day ')[1].split('-')[0])
            end_new = int(entry['day_range'].split('-')[1])
            current_entry['day_range'] = f"Day {start_current}-{end_new}"
        else:
            merged_itinerary.append(current_entry)
            current_entry = entry
    merged_itinerary.append(current_entry)
    
    return {"itinerary": merged_itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))