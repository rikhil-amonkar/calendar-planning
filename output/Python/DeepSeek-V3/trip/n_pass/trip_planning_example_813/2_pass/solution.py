import json
from itertools import permutations

def find_itinerary():
    # Cities and their required stay days (excluding transition days)
    city_stay_days = {
        'Seville': 4,  # Reduced by 1 for transition
        'Vilnius': 2,
        'Santorini': 1,
        'London': 1,
        'Stuttgart': 2,
        'Dublin': 2,
        'Frankfurt': 4
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
    
    # Constraints
    london_friends_day = (9, 10)
    stuttgart_relatives_day = (7, 9)
    
    # Total days
    total_days = 17
    
    # Generate all possible city orders (permutations)
    cities = list(city_stay_days.keys())
    
    # We'll try all permutations of the cities to find a valid itinerary
    for city_order in permutations(cities):
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        for city in city_order:
            if prev_city is not None:
                # Check if there's a direct flight
                if city not in connections[prev_city]:
                    valid = False
                    break
                
                # Add transition day (counts as last day of prev city and first day of next)
                itinerary.append({
                    "day_range": f"Day {current_day}",
                    "place": f"{prev_city} to {city}"
                })
                current_day += 1
            
            # Add stay in the city (remaining days after transition)
            stay_days = city_stay_days[city]
            if stay_days <= 0:
                valid = False
                break
                
            start_day = current_day
            end_day = current_day + stay_days - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            current_day = end_day + 1
            prev_city = city
        
        # Check if all days are used and constraints are met
        if valid and current_day - 1 == total_days:
            # Check London friends constraint
            london_ok = False
            stuttgart_ok = False
            for entry in itinerary:
                if entry['place'] == 'London':
                    day_range = entry['day_range']
                    if day_range.startswith('Day '):
                        days = day_range[4:].split('-')
                        start = int(days[0])
                        end = int(days[1]) if len(days) > 1 else start
                        if (start <= london_friends_day[1] and end >= london_friends_day[0]):
                            london_ok = True
                elif entry['place'] == 'Stuttgart':
                    day_range = entry['day_range']
                    if day_range.startswith('Day '):
                        days = day_range[4:].split('-')
                        start = int(days[0])
                        end = int(days[1]) if len(days) > 1 else start
                        if (start <= stuttgart_relatives_day[1] and end >= stuttgart_relatives_day[0]):
                            stuttgart_ok = True
            if london_ok and stuttgart_ok:
                return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found."}

# Run the function and print the result
print(json.dumps(find_itinerary()))