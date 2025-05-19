import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 32
    city_stays = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    # Fixed events
    fixed_events = {
        'Istanbul': (25, 29),
        'Krakow': (5, 9)
    }
    
    # Direct flights
    direct_flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Frankfurt', 'Hamburg', 'Munich'],
        'Stockholm': ['Oslo', 'Munich', 'Hamburg', 'Istanbul', 'Santorini', 'Krakow', 'Frankfurt'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Oslo', 'Munich', 'Stockholm', 'Hamburg'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence', 'Krakow', 'Vilnius'],
        'Hamburg': ['Stockholm', 'Munich', 'Istanbul', 'Oslo', 'Frankfurt'],
        'Vilnius': ['Istanbul', 'Frankfurt', 'Oslo', 'Munich', 'Krakow'],
        'Santorini': ['Stockholm', 'Oslo'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Oslo', 'Florence', 'Stockholm', 'Munich', 'Hamburg', 'Vilnius'],
        'Florence': ['Frankfurt', 'Munich'],
        'Istanbul': ['Krakow', 'Oslo', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg', 'Stockholm']
    }
    
    # All cities to visit
    cities = list(city_stays.keys())
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check fixed events first
        for city, (start, end) in fixed_events.items():
            if city not in perm:
                valid = False
                break
        
        if not valid:
            continue
        
        prev_city = None
        planned_days = {}
        
        # Try to build itinerary
        for city in perm:
            # Check if we can fly to this city
            if prev_city is not None and city not in direct_flights[prev_city]:
                valid = False
                break
            
            # Check fixed events
            if city in fixed_events:
                start, end = fixed_events[city]
                duration = end - start + 1
                
                # Check if the stay matches required duration
                if city_stays[city] != duration:
                    valid = False
                    break
                
                # Check if we can fit this stay
                if start < current_day:
                    valid = False
                    break
                
                # Add travel day if needed
                if prev_city is not None and prev_city != city:
                    travel_day = start - 1
                    if travel_day < current_day:
                        valid = False
                        break
                    
                    itinerary.append({
                        'day_range': f'Day {current_day}-{travel_day - 1}',
                        'place': prev_city
                    })
                    itinerary.append({
                        'flying': f'Day {travel_day}-{travel_day}',
                        'from': prev_city,
                        'to': city
                    })
                    current_day = travel_day + 1
                else:
                    current_day = start
                
                itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + duration - 1}',
                    'place': city
                })
                current_day += duration
                prev_city = city
                planned_days[city] = True
            else:
                # Handle non-fixed cities
                duration = city_stays[city]
                
                # Add travel day if needed
                if prev_city is not None and prev_city != city:
                    itinerary.append({
                        'day_range': f'Day {current_day}-{current_day}',
                        'flying': f'Day {current_day}-{current_day}',
                        'from': prev_city,
                        'to': city
                    })
                    current_day += 1
                
                itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + duration - 1}',
                    'place': city
                })
                current_day += duration
                prev_city = city
                planned_days[city] = True
        
        # Check if all cities are planned and total days is 32
        if valid and len(planned_days) == len(cities) and current_day - 1 == total_days:
            print(json.dumps(itinerary, indent=2))
            return
    
    # If no valid itinerary found (though the problem states one exists)
    print(json.dumps([{"error": "No valid itinerary found"}], indent=2))

if __name__ == "__main__":
    main()