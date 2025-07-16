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
    
    # Define fixed events
    fixed_events = [
        {'city': 'Istanbul', 'day_range': (25, 29)},
        {'city': 'Krakow', 'day_range': (5, 9)}
    ]
    
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
    
    # Generate all possible city orders with fixed events in correct positions
    cities = list(city_durations.keys())
    other_cities = [c for c in cities if c not in ['Krakow', 'Istanbul']]
    
    # We'll try permutations where Krakow is early and Istanbul is late
    for perm in permutations(other_cities, len(other_cities)):
        # Try inserting fixed cities at different positions
        for k_pos in range(0, 3):  # Krakow in first 3 positions
            for i_pos in range(5, len(perm)+2):  # Istanbul in later positions
                order = list(perm)
                order.insert(k_pos, 'Krakow')
                order.insert(i_pos, 'Istanbul')
                
                itinerary = []
                current_day = 1
                prev_city = None
                valid = True
                
                for city in order:
                    # Check if we need a flight day
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
                    for event in fixed_events:
                        if event['city'] == city:
                            start, end = event['day_range']
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