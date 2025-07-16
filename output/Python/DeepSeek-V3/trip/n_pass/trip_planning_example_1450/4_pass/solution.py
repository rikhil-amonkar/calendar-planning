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
    
    # Calculate total days needed (excluding flight days)
    total_stay_days = sum(city_durations.values())
    
    # We need to account for flight days between cities
    # For 10 cities, there will be 9 flight days (since we start and end somewhere)
    # So total days = total_stay_days + (num_cities - 1)
    # 10 cities: 3+5+2+5+5+5+2+5+4+5 = 41 stay days + 9 flight days = 50 days
    # This exceeds 32 days, so we need to visit fewer cities
    
    # Since we must include Istanbul and Krakow, let's try visiting 6 cities total
    # (including Istanbul and Krakow)
    # 6 cities: ~20 stay days + 5 flight days = ~25 days (still too low)
    # 7 cities: ~25 stay days + 6 flight days = ~31 days
    # 8 cities: ~30 stay days + 7 flight days = ~37 days (too high)
    # So 7 cities seems most promising
    
    # Let's try all combinations of 5 additional cities (since we must include Istanbul and Krakow)
    other_cities = [c for c in city_durations.keys() if c not in ['Istanbul', 'Krakow']]
    
    for selected in permutations(other_cities, 5):
        cities_to_visit = ['Krakow'] + list(selected) + ['Istanbul']
        
        # Try all permutations of this city order (with Krakow first and Istanbul last)
        for city_order in permutations(cities_to_visit[1:-1], len(cities_to_visit)-2):
            city_order = ['Krakow'] + list(city_order) + ['Istanbul']
            
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
                    if current_day > 32:
                        valid = False
                        break
                
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
                
                if current_day > 32:
                    valid = False
                    break
            
            # Check exact 32 days
            if valid and current_day - 1 == 32:
                print(json.dumps({'itinerary': itinerary}))
                return
    
    # If no valid itinerary found
    print(json.dumps({'itinerary': [{'day_range': 'Day 1-32', 'place': 'No valid itinerary found'}]}))

if __name__ == "__main__":
    main()