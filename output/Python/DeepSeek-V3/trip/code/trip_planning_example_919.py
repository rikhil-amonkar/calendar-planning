import json
from itertools import permutations

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Vienna': {'days': 4, 'constraints': [{'day': 1, 'action': 'conference'}, {'day': 4, 'action': 'conference'}]},
        'Milan': {'days': 2},
        'Rome': {'days': 3},
        'Riga': {'days': 2},
        'Lisbon': {'days': 3, 'constraints': [{'start': 11, 'end': 13}]},
        'Vilnius': {'days': 4},
        'Oslo': {'days': 3, 'constraints': [{'start': 13, 'end': 15}]}
    }
    
    # Define direct flights as a graph
    flights = {
        'Riga': ['Oslo', 'Milan', 'Vilnius', 'Lisbon', 'Vienna', 'Rome'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Milan', 'Vienna', 'Vilnius'],
        'Rome': ['Oslo', 'Riga', 'Lisbon', 'Vienna'],
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Lisbon': ['Vienna', 'Oslo', 'Rome', 'Riga', 'Milan'],
        'Vilnius': ['Vienna', 'Oslo', 'Riga', 'Milan']
    }
    
    # Generate all possible permutations of cities
    city_names = list(cities.keys())
    all_permutations = permutations(city_names)
    
    valid_itineraries = []
    
    for perm in all_permutations:
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        for city in perm:
            # Check if we can fly to this city from previous
            if prev_city is not None and city not in flights[prev_city]:
                valid = False
                break
            
            # Add flight if not first city
            if prev_city is not None:
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 0  # Assume flight doesn't take a full day
            
            # Check constraints for this city
            city_info = cities[city]
            days_needed = city_info['days']
            end_day = current_day + days_needed - 1
            
            # Check specific constraints
            if 'constraints' in city_info:
                for constraint in city_info['constraints']:
                    if 'day' in constraint:
                        day = constraint['day']
                        if not (current_day <= day <= end_day):
                            valid = False
                            break
                    elif 'start' in constraint and 'end' in constraint:
                        start = constraint['start']
                        end = constraint['end']
                        # The constraint range must be fully within the stay
                        if not (current_day <= start and end <= end_day):
                            valid = False
                            break
                if not valid:
                    break
            
            # Add city stay
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            current_day = end_day + 1
            prev_city = city
        
        # Check total days
        if valid and (current_day - 1) <= 15:
            valid_itineraries.append(itinerary)
    
    # Select the first valid itinerary (can be optimized further)
    if valid_itineraries:
        return valid_itineraries[0]
    else:
        return None

def main():
    itinerary = find_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()