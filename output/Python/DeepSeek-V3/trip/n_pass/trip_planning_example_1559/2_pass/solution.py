import json
from itertools import permutations

def main():
    # Define the cities and their required days
    city_days = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    # Define the constraints (city: (start_day, end_day))
    constraints = {
        'Valencia': (3, 4),
        'Oslo': (13, 15),
        'Seville': (5, 9),
        'Mykonos': (21, 25)
    }
    
    # Define the direct flights
    direct_flights = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Tallinn', 'Seville', 'Prague'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo'],
        'Nice': ['Lyon', 'Oslo', 'Paris', 'Lisbon', 'Mykonos'],
        'Tallinn': ['Oslo', 'Prague', 'Paris'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Valencia', 'Paris', 'Tallinn'],
        'Oslo': ['Tallinn', 'Paris', 'Prague', 'Nice', 'Lyon'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Seville', 'Prague'],
        'Seville': ['Lisbon', 'Paris', 'Valencia'],
        'Mykonos': ['Nice']
    }
    
    # Generate all possible permutations of the cities
    cities = list(city_days.keys())
    
    # We'll try to find a valid itinerary by checking permutations
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        
        # Build the itinerary
        for city in perm:
            days_needed = city_days[city]
            day_end = current_day + days_needed - 1
            itinerary.append({
                'place': city,
                'day_start': current_day,
                'day_end': day_end
            })
            current_day = day_end + 1
        
        # Check total days
        if current_day - 1 != 25:
            continue
        
        # Check constraints
        for city, (start, end) in constraints.items():
            found = False
            for entry in itinerary:
                if entry['place'] == city:
                    # Check if the city's stay overlaps with the required window
                    if not (entry['day_end'] < start or entry['day_start'] > end):
                        found = True
                        break
            if not found:
                valid = False
                break
        
        if not valid:
            continue
        
        # Check flight connections
        for i in range(len(perm) - 1):
            current_city = perm[i]
            next_city = perm[i + 1]
            if next_city not in direct_flights.get(current_city, []):
                valid = False
                break
        
        if valid:
            # Format the output as required
            formatted_itinerary = []
            for entry in itinerary:
                formatted_itinerary.append({
                    'day_range': f"Day {entry['day_start']}-{entry['day_end']}",
                    'place': entry['place']
                })
            print(json.dumps({'itinerary': formatted_itinerary}, indent=2))
            return
    
    # If no valid itinerary found (though the problem states one exists)
    print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()