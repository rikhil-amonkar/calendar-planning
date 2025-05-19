import json
from itertools import permutations

def find_itinerary():
    total_days = 23
    cities = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    
    # Constraints
    geneva_conference = (1, 7)
    oslo_relatives = (19, 23)
    
    # Direct flights
    flights = {
        'Paris': ['Oslo', 'Porto', 'Geneva', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Porto', 'Oslo'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    # Generate all possible permutations of the 5 cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        for city in perm:
            if prev_city is not None:
                # Check if flight is possible
                if city not in flights[prev_city]:
                    valid = False
                    break
                # Add flight day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
            
            # Determine stay duration
            stay_duration = cities[city]
            
            # Apply constraints
            if city == 'Geneva':
                # Must be there from day 1-7
                if current_day > geneva_conference[0] or (current_day + stay_duration - 1) < geneva_conference[1]:
                    valid = False
                    break
            elif city == 'Oslo':
                # Must be there between day 19-23
                if (current_day + stay_duration - 1) < oslo_relatives[0] or current_day > oslo_relatives[1]:
                    valid = False
                    break
            
            # Add stay
            end_day = current_day + stay_duration - 1
            if end_day > total_days:
                valid = False
                break
            
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            current_day = end_day + 1
            prev_city = city
        
        if valid and current_day == total_days + 1:
            # Check all cities are visited
            visited_cities = {item['place'] for item in itinerary if 'place' in item}
            if len(visited_cities) == 5:
                return itinerary
    
    return None

def main():
    itinerary = find_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()