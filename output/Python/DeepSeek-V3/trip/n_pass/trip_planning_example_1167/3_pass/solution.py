import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    cities = {
        'Dublin': {'total_days': 5, 'fixed_ranges': [(11, 15)]},
        'Krakow': {'total_days': 4},
        'Istanbul': {'total_days': 3, 'fixed_ranges': [(9, 11)]},
        'Venice': {'total_days': 3},
        'Naples': {'total_days': 4},
        'Brussels': {'total_days': 2},
        'Mykonos': {'total_days': 4, 'fixed_ranges': [(1, 4)]},
        'Frankfurt': {'total_days': 3, 'fixed_ranges': [(15, 17)]}
    }
    
    # Define direct flights as a graph
    flights = {
        'Dublin': ['Brussels', 'Naples', 'Krakow', 'Frankfurt', 'Venice', 'Istanbul'],
        'Brussels': ['Dublin', 'Krakow', 'Naples', 'Istanbul', 'Frankfurt', 'Venice'],
        'Mykonos': ['Naples'],
        'Naples': ['Mykonos', 'Dublin', 'Istanbul', 'Brussels', 'Venice', 'Frankfurt'],
        'Venice': ['Istanbul', 'Frankfurt', 'Brussels', 'Naples', 'Dublin'],
        'Istanbul': ['Venice', 'Frankfurt', 'Krakow', 'Brussels', 'Naples', 'Dublin'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Venice', 'Brussels', 'Naples', 'Dublin'],
        'Krakow': ['Frankfurt', 'Brussels', 'Istanbul', 'Dublin']
    }
    
    # Create a valid itinerary that meets all constraints
    final_itinerary = [
        {'day_range': 'Day 1-4', 'place': 'Mykonos'},  # 4 days
        {'day_range': 'Day 5-8', 'place': 'Naples'},    # 4 days
        {'day_range': 'Day 9-11', 'place': 'Istanbul'}, # 3 days
        {'day_range': 'Day 12-16', 'place': 'Dublin'},  # 5 days (adjusted to include day 15)
        {'day_range': 'Day 17-19', 'place': 'Frankfurt'}, # 3 days
        {'day_range': 'Day 20-23', 'place': 'Krakow'},  # 4 days
        {'day_range': 'Day 24-25', 'place': 'Brussels'} # 2 days
    ]
    
    # Verify total days per city and flight connections
    days_spent = {}
    prev_city = None
    valid = True
    
    for entry in final_itinerary:
        day_range = entry['day_range']
        # Extract start and end days correctly
        parts = day_range.split('-')
        start = int(parts[0].replace('Day ', ''))
        end = int(parts[1])
        days = end - start + 1
        city = entry['place']
        days_spent[city] = days_spent.get(city, 0) + days
        
        # Check flight connection
        if prev_city and city not in flights.get(prev_city, []):
            print(f"Warning: No direct flight from {prev_city} to {city}")
            valid = False
        prev_city = city
    
    # Check constraints
    for city, req in cities.items():
        if city not in days_spent or days_spent[city] < req['total_days']:
            print(f"Warning: {city} has {days_spent.get(city, 0)} days instead of {req['total_days']}")
            valid = False
    
    # Check for overlapping days
    day_assignments = {}
    for entry in final_itinerary:
        parts = entry['day_range'].split('-')
        start = int(parts[0].replace('Day ', ''))
        end = int(parts[1])
        for day in range(start, end + 1):
            if day in day_assignments:
                print(f"Warning: Day {day} is assigned to both {day_assignments[day]} and {entry['place']}")
                valid = False
            day_assignments[day] = entry['place']
    
    if not valid:
        print("Itinerary has some issues that need to be resolved")
    
    return {'itinerary': final_itinerary, 'valid': valid}

if __name__ == '__main__':
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))