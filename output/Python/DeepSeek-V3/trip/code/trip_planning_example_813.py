import json
from itertools import permutations

def find_valid_itinerary():
    # Cities and their required days
    cities = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    # Direct flight connections
    connections = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin'],
        'Santorini': ['London', 'Dublin']
    }
    
    # Special constraints
    london_friends_days = (9, 10)
    stuttgart_relatives_days = (7, 9)
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        for city in perm:
            if prev_city is not None:
                # Check if there's a direct flight
                if city not in connections[prev_city]:
                    valid = False
                    break
                # Add flight day
                itinerary.append({
                    'day_range': f'Day {current_day}-{current_day}',
                    'flying': True,
                    'from': prev_city,
                    'to': city
                })
                current_day += 1
            
            # Add stay in city
            stay_days = cities[city]
            end_day = current_day + stay_days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            # Check special constraints
            if city == 'London':
                if not (current_day <= london_friends_days[0] and end_day >= london_friends_days[1]):
                    valid = False
                    break
            if city == 'Stuttgart':
                if not (current_day <= stuttgart_relatives_days[0] and end_day >= stuttgart_relatives_days[1]):
                    valid = False
                    break
            
            current_day = end_day + 1
            prev_city = city
        
        # Check total days
        if valid and (current_day - 1) == 17:
            # Reconstruct itinerary in desired format
            final_itinerary = []
            for item in itinerary:
                if 'flying' in item:
                    final_itinerary.append({
                        'day_range': item['day_range'],
                        'from': item['from'],
                        'to': item['to']
                    })
                else:
                    final_itinerary.append({
                        'day_range': item['day_range'],
                        'place': item['place']
                    })
            return final_itinerary
    
    return None

def main():
    itinerary = find_valid_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()