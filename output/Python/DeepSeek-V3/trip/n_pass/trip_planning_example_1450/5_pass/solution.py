import json
from itertools import permutations

def main():
    # Define city stay durations
    city_durations = {
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
    
    # Define fixed events with their required days
    fixed_events = {
        'Istanbul': {'day_range': (25, 29)},  # Must be in Istanbul days 25-29
        'Krakow': {'day_range': (5, 9)}      # Must be in Krakow days 5-9
    }
    
    # Define direct flights
    direct_flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Frankfurt', 'Hamburg', 'Munich'],
        'Stockholm': ['Oslo', 'Munich', 'Hamburg', 'Istanbul', 'Santorini', 'Krakow', 'Frankfurt'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Oslo', 'Munich', 'Stockholm'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence', 'Krakow', 'Vilnius'],
        'Hamburg': ['Stockholm', 'Munich', 'Istanbul', 'Frankfurt', 'Oslo'],
        'Vilnius': ['Istanbul', 'Frankfurt', 'Oslo', 'Munich', 'Krakow'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Oslo', 'Stockholm', 'Florence', 'Munich', 'Hamburg', 'Vilnius'],
        'Florence': ['Frankfurt', 'Munich'],
        'Istanbul': ['Krakow', 'Oslo', 'Stockholm', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg'],
        'Santorini': ['Stockholm', 'Oslo']
    }
    
    # We must include Istanbul and Krakow, so let's try combinations of 4 cities total
    other_cities = [c for c in city_durations.keys() if c not in ['Istanbul', 'Krakow']]
    
    for city1, city2 in permutations(other_cities, 2):
        cities_to_visit = ['Krakow', city1, city2, 'Istanbul']
        
        # Calculate total days needed
        total_days = sum(city_durations[c] for c in cities_to_visit) + (len(cities_to_visit) - 1
        
        if total_days != 32:
            continue  # Skip if not exactly 32 days
            
        # Try all permutations of the middle cities
        for middle_order in permutations(cities_to_visit[1:-1]):
            city_order = [cities_to_visit[0]] + list(middle_order) + [cities_to_visit[-1]]
            
            itinerary = []
            current_day = 1
            prev_city = None
            valid = True
            
            for city in city_order:
                # Flight day if needed
                if prev_city is not None and city != prev_city:
                    if city not in direct_flights[prev_city]:
                        valid = False
                        break
                    itinerary.append({
                        'day_range': f"Day {current_day}",
                        'place': f"{prev_city} to {city}"
                    })
                    current_day += 1
                
                # Get stay duration
                duration = city_durations[city]
                
                # Check fixed events for this city
                if city in fixed_events:
                    start, end = fixed_events[city]['day_range']
                    required_days = end - start + 1
                    if duration < required_days:
                        valid = False
                        break
                    # Check if stay covers the event
                    stay_start = current_day
                    stay_end = current_day + duration - 1
                    if not (stay_start <= start and stay_end >= end):
                        valid = False
                        break
                
                if not valid:
                    break
                
                # Add the stay
                if duration == 1:
                    day_str = f"Day {current_day}"
                else:
                    day_str = f"Day {current_day}-{current_day + duration - 1}"
                
                itinerary.append({
                    'day_range': day_str,
                    'place': city
                })
                current_day += duration
                prev_city = city
            
            # Check exact 32 days
            if valid and current_day - 1 == 32:
                print(json.dumps({'itinerary': itinerary}))
                return
    
    # If no valid itinerary found
    print(json.dumps({'itinerary': [{'day_range': 'Day 1-32', 'place': 'No valid itinerary found'}]}))

if __name__ == "__main__":
    main()