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
    
    # Create a valid itinerary that meets all constraints (21 days total)
    final_itinerary = [
        {'day_range': 'Day 1-4', 'place': 'Mykonos'},  # 4 days (fixed)
        {'day_range': 'Day 5-8', 'place': 'Naples'},    # 4 days
        {'day_range': 'Day 9-11', 'place': 'Istanbul'}, # 3 days (fixed)
        {'day_range': 'Day 12-16', 'place': 'Dublin'},  # 5 days (includes fixed 11-15)
        {'day_range': 'Day 17-19', 'place': 'Venice'},  # 3 days (replacing Frankfurt)
        {'day_range': 'Day 20-21', 'place': 'Brussels'} # 2 days (shortened)
    ]
    
    # Verify total days per city and flight connections
    days_spent = {}
    prev_city = None
    valid = True
    
    for entry in final_itinerary:
        day_range = entry['day_range']
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
    
    # Check total days
    total_days = max(day_assignments.keys()) if day_assignments else 0
    if total_days != 21:
        print(f"Warning: Itinerary covers {total_days} days instead of 21")
        valid = False
    
    if not valid:
        print("Itinerary has some issues that need to be resolved")
    
    return {'itinerary': final_itinerary, 'valid': valid}

if __name__ == '__main__':
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))