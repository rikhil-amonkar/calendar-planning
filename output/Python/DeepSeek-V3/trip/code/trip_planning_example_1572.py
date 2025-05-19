import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 23
    cities = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Berlin': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    
    # Constraints
    constraints = [
        {'city': 'Berlin', 'day_range': (1, 2)},
        {'city': 'Stockholm', 'day_range': (20, 22)},
        {'city': 'Nice', 'day_range': (12, 13)}
    ]
    
    # Direct flights
    direct_flights = {
        'Paris': ['Stockholm', 'Seville', 'Zurich', 'Nice', 'Lyon', 'Riga', 'Naples'],
        'Stockholm': ['Paris', 'Riga', 'Zurich', 'Berlin', 'Nice', 'Milan'],
        'Seville': ['Paris', 'Milan'],
        'Naples': ['Zurich', 'Milan', 'Paris', 'Nice', 'Berlin'],
        'Nice': ['Riga', 'Paris', 'Zurich', 'Stockholm', 'Naples', 'Lyon', 'Berlin'],
        'Riga': ['Nice', 'Paris', 'Stockholm', 'Zurich', 'Berlin', 'Milan'],
        'Berlin': ['Milan', 'Stockholm', 'Paris', 'Naples', 'Nice', 'Riga', 'Zurich'],
        'Milan': ['Berlin', 'Paris', 'Naples', 'Riga', 'Zurich', 'Stockholm', 'Seville'],
        'Zurich': ['Naples', 'Paris', 'Nice', 'Milan', 'Stockholm', 'Riga', 'Berlin'],
        'Lyon': ['Paris', 'Nice']
    }
    
    # Fix typo in direct_flights
    direct_flights_fixed = {}
    for city, destinations in direct_flights.items():
        fixed_destinations = []
        for dest in destinations:
            if dest == 'Zurich':
                fixed_destinations.append('Zurich')
            elif dest == 'Milan':
                fixed_destinations.append('Milan')
            else:
                fixed_destinations.append(dest)
        direct_flights[city] = fixed_destinations
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    # Function to check if flight is possible
    def can_fly(from_city, to_city):
        return to_city in direct_flights.get(from_city, [])
    
    # Function to check constraints
    def satisfies_constraints(itinerary):
        for constraint in constraints:
            city = constraint['city']
            start, end = constraint['day_range']
            found = False
            current_day = 1
            for entry in itinerary:
                if 'place' in entry:
                    entry_start = current_day
                    day_range = entry['day_range']
                    parts = day_range.split('-')
                    start_day = int(parts[0].replace('Day ', ''))
                    end_day = int(parts[1].replace('Day ', ''))
                    duration = end_day - start_day + 1
                    entry_end = entry_start + duration - 1
                    if entry['place'] == city:
                        if not (entry_end < start or entry_start > end):
                            found = True
                            break
                    current_day = entry_end + 1
                else:
                    current_day += 1
            if not found:
                return False
        return True
    
    # Find a valid itinerary
    valid_itinerary = None
    for order in possible_orders:
        itinerary = []
        current_day = 1
        prev_city = None
        
        valid = True
        for city in order:
            if prev_city is not None:
                if not can_fly(prev_city, city):
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1
            
            duration = cities[city]
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + duration - 1}',
                'place': city
            })
            current_day += duration
            prev_city = city
        
        if valid and current_day - 1 <= total_days and satisfies_constraints(itinerary):
            valid_itinerary = itinerary
            break
    
    # Output the result
    print(json.dumps(valid_itinerary, indent=2))

if __name__ == "__main__":
    main()