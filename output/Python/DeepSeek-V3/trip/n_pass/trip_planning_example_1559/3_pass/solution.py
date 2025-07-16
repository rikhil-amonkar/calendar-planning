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
    
    # First place the constrained cities
    constrained_cities = list(constraints.keys())
    other_cities = [city for city in city_days.keys() if city not in constraints]
    
    # Generate all possible permutations of the other cities
    for perm in permutations(other_cities):
        # Create a timeline of 25 days
        timeline = [None] * 25
        valid = True
        
        # Place constrained cities first
        for city in constrained_cities:
            start, end = constraints[city]
            days_needed = city_days[city]
            
            # Check if the required days fit in the constraint window
            if end - start + 1 < days_needed:
                valid = False
                break
                
            # Place the city in the earliest possible position within its window
            placed = False
            for day in range(start, end - days_needed + 2):
                if all(timeline[d-1] is None for d in range(day, day + days_needed)):
                    for d in range(day, day + days_needed):
                        timeline[d-1] = city
                    placed = True
                    break
            
            if not placed:
                valid = False
                break
        
        if not valid:
            continue
        
        # Now try to place the other cities
        current_day = 1
        for city in perm:
            days_needed = city_days[city]
            placed = False
            
            # Find the next available block of days
            while current_day <= 26 - days_needed:
                if all(timeline[d-1] is None for d in range(current_day, current_day + days_needed)):
                    for d in range(current_day, current_day + days_needed):
                        timeline[d-1] = city
                    placed = True
                    current_day += days_needed
                    break
                current_day += 1
            
            if not placed:
                valid = False
                break
        
        if not valid:
            continue
        
        # Check if all days are filled
        if None in timeline:
            continue
        
        # Build the itinerary
        itinerary = []
        current_city = timeline[0]
        start_day = 1
        for day in range(1, 26):
            if day < 25 and timeline[day] == current_city:
                continue
            else:
                itinerary.append({
                    'place': current_city,
                    'day_start': start_day,
                    'day_end': day
                })
                if day < 25:
                    current_city = timeline[day]
                    start_day = day + 1
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if next_city not in direct_flights.get(current_city, []):
                valid = False
                break
        
        if valid:
            # Format the output
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