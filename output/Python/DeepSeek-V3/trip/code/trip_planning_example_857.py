import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 18
    cities = {
        'Porto': {'days': 2},
        'Geneva': {'days': 3},
        'Mykonos': {'days': 3, 'constraint': (10, 12)},
        'Manchester': {'days': 4, 'constraint': (15, 18)},
        'Hamburg': {'days': 5},
        'Naples': {'days': 5},
        'Frankfurt': {'days': 2, 'constraint': (5, 6)}
    }
    
    # Direct flights graph
    direct_flights = {
        'Hamburg': ['Frankfurt', 'Porto', 'Geneva', 'Manchester'],
        'Frankfurt': ['Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester'],
        'Porto': ['Hamburg', 'Frankfurt', 'Geneva', 'Manchester'],
        'Geneva': ['Hamburg', 'Frankfurt', 'Porto', 'Mykonos', 'Manchester', 'Naples'],
        'Mykonos': ['Geneva', 'Naples'],
        'Naples': ['Mykonos', 'Frankfurt', 'Geneva', 'Manchester'],
        'Manchester': ['Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg']
    }
    
    # Correct typo in city name
    direct_flights['Frankfurt'].remove('Naples')
    direct_flights['Frankfurt'].append('Naples')
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    possible_sequences = permutations(city_names)
    
    valid_itineraries = []
    
    for sequence in possible_sequences:
        current_day = 1
        itinerary = []
        prev_city = None
        valid = True
        
        for city in sequence:
            if prev_city is not None:
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1  # Travel day
            
            stay_days = cities[city]['days']
            day_range = f'Day {current_day}-{current_day + stay_days - 1}'
            itinerary.append({
                'day_range': day_range,
                'place': city
            })
            
            # Check constraints
            if 'constraint' in cities[city]:
                start, end = cities[city]['constraint']
                if not (current_day <= start and current_day + stay_days - 1 >= end):
                    valid = False
                    break
            
            if city == 'Frankfurt':
                frankfurt_start = current_day
                frankfurt_end = current_day + stay_days - 1
                if not (5 <= frankfurt_start <= 6 or 5 <= frankfurt_end <= 6 or 
                        (frankfurt_start <= 5 and frankfurt_end >= 6)):
                    valid = False
                    break
            
            current_day += stay_days
            prev_city = city
        
        if valid and current_day - 1 == total_days:
            valid_itineraries.append(itinerary)
    
    # Select the first valid itinerary (can be optimized further)
    if valid_itineraries:
        output = valid_itineraries[0]
    else:
        output = []
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()