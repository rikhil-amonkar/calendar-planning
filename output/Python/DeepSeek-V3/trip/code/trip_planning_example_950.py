import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        'Mykonos': 3,
        'Riga': 3,
        'Munich': 4,
        'Bucharest': 4,
        'Rome': 4,
        'Nice': 3,
        'Krakow': 2
    }
    
    # Special constraints
    constraints = [
        {'place': 'Rome', 'day_range': (1, 4)},
        {'place': 'Mykonos', 'day_range': (4, 6)},
        {'place': 'Krakow', 'day_range': (16, 17)}
    ]
    
    # Direct flights (undirected graph)
    flights = {
        'Nice': ['Riga', 'Rome', 'Mykonos', 'Munich'],
        'Riga': ['Nice', 'Bucharest', 'Rome', 'Munich'],
        'Bucharest': ['Riga', 'Munich', 'Rome'],
        'Munich': ['Bucharest', 'Mykonos', 'Rome', 'Nice', 'Riga', 'Krakow'],
        'Rome': ['Nice', 'Munich', 'Mykonos', 'Bucharest', 'Riga'],
        'Mykonos': ['Munich', 'Nice', 'Rome'],
        'Krakow': ['Munich']
    }
    
    # Generate all possible city orders that meet the constraints
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if the order meets the constraints
        # Rome must be first (since conference is day 1-4)
        if order[0] != 'Rome':
            continue
        
        # Mykonos must be after Rome but before day 6
        mykonos_pos = order.index('Mykonos')
        if mykonos_pos <= 0 or mykonos_pos >= 5:  # Must be in first 5 cities (since day 6 is early)
            continue
        
        # Krakow must be last (since show is day 16-17)
        if order[-1] != 'Krakow':
            continue
        
        # Check flight connections
        valid_flights = True
        for i in range(len(order) - 1):
            if order[i+1] not in flights[order[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Now try to assign days
        itinerary = []
        current_day = 1
        
        # Assign Rome first (days 1-4)
        rome_days = (1, 4)
        itinerary.append({
            'day_range': f'Day {rome_days[0]}-{rome_days[1]}',
            'place': 'Rome'
        })
        current_day = rome_days[1] + 1
        
        # Now assign other cities
        remaining_cities = [c for c in order if c != 'Rome']
        
        # We know Mykonos must be next (since wedding is day 4-6)
        if 'Mykonos' in remaining_cities:
            mykonos_pos_in_remaining = remaining_cities.index('Mykonos')
            if mykonos_pos_in_remaining != 0:
                # Move Mykonos to front
                remaining_cities.remove('Mykonos')
                remaining_cities.insert(0, 'Mykonos')
        
        # Assign Mykonos (days 4-6)
        if remaining_cities[0] == 'Mykonos':
            mykonos_days = (4, 6)
            itinerary.append({
                'day_range': f'Day {mykonos_days[0]}-{mykonos_days[1]}',
                'place': 'Mykonos'
            })
            current_day = mykonos_days[1] + 1
            remaining_cities.pop(0)
        
        # Assign other cities
        for city in remaining_cities[:-1]:  # all except Krakow
            duration = cities[city]
            end_day = current_day + duration - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            # Add flight to next city
            next_city = remaining_cities[remaining_cities.index(city)+1]
            itinerary.append({
                'flying': f'Day {end_day}-{end_day}',
                'from': city,
                'to': next_city
            })
            current_day = end_day + 1
        
        # Assign Krakow last (days 16-17)
        if remaining_cities[-1] == 'Krakow':
            krakow_days = (16, 17)
            if current_day <= krakow_days[0]:
                # Fill gap if needed
                if current_day < krakow_days[0]:
                    # Need to assign some city in between
                    # This is getting complex, skip for now
                    continue
                itinerary.append({
                    'day_range': f'Day {krakow_days[0]}-{krakow_days[1]}',
                    'place': 'Krakow'
                })
            else:
                continue
        
        # Check if all cities are covered
        covered_cities = set([item['place'] for item in itinerary if 'place' in item])
        if covered_cities == set(city_names):
            valid_itineraries.append(itinerary)
    
    # Select the first valid itinerary (in a real scenario, we might optimize further)
    if valid_itineraries:
        return valid_itineraries[0]
    else:
        return []

def main():
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()