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
    
    # Generate all possible city orders (limit permutations to make it feasible)
    cities = list(city_durations.keys())
    # We'll try a limited set of permutations that include fixed cities early
    fixed_cities = ['Krakow', 'Istanbul']
    other_cities = [c for c in cities if c not in fixed_cities]
    possible_orders = []
    
    # Generate permutations where Krakow and Istanbul appear in reasonable positions
    for perm in permutations(other_cities):
        # Insert fixed cities at positions that might work
        for k_pos in range(0, 3):
            for i_pos in range(5, 8):
                new_order = list(perm)
                new_order.insert(k_pos, 'Krakow')
                new_order.insert(i_pos, 'Istanbul')
                possible_orders.append(new_order)
                if len(possible_orders) >= 1000:  # Limit permutations to try
                    break
            if len(possible_orders) >= 1000:
                break
        if len(possible_orders) >= 1000:
            break
    
    # Find a valid itinerary
    valid_itinerary = None
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True
        
        # Build itinerary
        for city in order:
            # Check if we need to move to this city
            if prev_city is not None and city != prev_city:
                # Check if there's a direct flight
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                # Transition day (counts as 1 day)
                itinerary.append({
                    'day_range': f"Day {current_day}",
                    'place': f"{prev_city} to {city}"
                })
                current_day += 1
            
            # Add stay duration
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
        
        # Check total days exactly equals 32
        if valid and current_day - 1 == 32:
            valid_itinerary = itinerary
            break
    
    # Output the itinerary
    if valid_itinerary:
        print(json.dumps({'itinerary': valid_itinerary}))
    else:
        print(json.dumps({'itinerary': [{'day_range': 'Day 1-32', 'place': 'No valid itinerary found'}]}))

if __name__ == "__main__":
    main()