import json
from itertools import permutations

def main():
    # Define cities and their required days
    cities = {
        'Dublin': 5,
        'Krakow': 4,
        'Istanbul': 3,
        'Venice': 3,
        'Naples': 4,
        'Brussels': 2,
        'Mykonos': 4,
        'Frankfurt': 3
    }
    
    # Define direct flights as a graph
    flight_graph = {
        'Dublin': ['Brussels', 'Naples', 'Krakow', 'Istanbul', 'Frankfurt', 'Venice'],
        'Brussels': ['Dublin', 'Krakow', 'Naples', 'Istanbul', 'Frankfurt', 'Venice'],
        'Mykonos': ['Naples'],
        'Naples': ['Mykonos', 'Dublin', 'Istanbul', 'Brussels', 'Venice', 'Frankfurt'],
        'Venice': ['Istanbul', 'Frankfurt', 'Brussels', 'Naples', 'Dublin'],
        'Frankfurt': ['Krakow', 'Brussels', 'Istanbul', 'Venice', 'Naples', 'Dublin'],
        'Krakow': ['Frankfurt', 'Brussels', 'Istanbul', 'Dublin'],
        'Istanbul': ['Venice', 'Frankfurt', 'Naples', 'Brussels', 'Krakow', 'Dublin']
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Mykonos', (1, 4)),
        ('Dublin', (11, 15)),
        ('Istanbul', (9, 11)),
        ('Frankfurt', (15, 17))
    ]
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    best_itinerary = None
    best_score = float('inf')  # Lower score is better
    
    for order in possible_orders:
        # Check if Mykonos is first (due to day 1-4 constraint)
        if order[0] != 'Mykonos':
            continue
        
        # Try to build itinerary
        itinerary = []
        current_day = 1
        valid = True
        
        # Assign fixed constraints first
        fixed_days = set()
        for city, (start, end) in fixed_constraints:
            if city not in order:
                valid = False
                break
            days_needed = end - start + 1
            if cities[city] < days_needed:
                valid = False
                break
            itinerary.append({
                'day_range': f"Day {start}-{end}",
                'place': city
            })
            fixed_days.update(range(start, end + 1))
            current_day = max(current_day, end + 1)
        
        if not valid:
            continue
        
        # Assign remaining cities and days
        remaining_cities = [city for city in order if city not in [x['place'] for x in itinerary]]
        remaining_days = 21 - len(fixed_days)
        remaining_city_days = {city: cities[city] for city in remaining_cities}
        
        # Subtract days already allocated in fixed constraints
        for entry in itinerary:
            city = entry['place']
            start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
            days_spent = end - start + 1
            if city in remaining_city_days:
                remaining_city_days[city] -= days_spent
                if remaining_city_days[city] < 0:
                    valid = False
                    break
                if remaining_city_days[city] == 0:
                    del remaining_city_days[city]
        
        if not valid:
            continue
        
        # Assign remaining days to remaining cities
        temp_day = 1
        temp_itinerary = []
        allocated = set()
        
        # Helper function to find next available days
        def find_available_days(length):
            nonlocal temp_day
            start = temp_day
            while True:
                # Find contiguous block of 'length' days not in fixed_days
                end = start + length - 1
                if end > 21:
                    return None
                if all(day not in fixed_days for day in range(start, end + 1)):
                    return (start, end)
                start += 1
        
        for city in order:
            if city in remaining_city_days and remaining_city_days[city] > 0:
                days_needed = remaining_city_days[city]
                block = find_available_days(days_needed)
                if not block:
                    valid = False
                    break
                start, end = block
                temp_itinerary.append({
                    'day_range': f"Day {start}-{end}",
                    'place': city
                })
                fixed_days.update(range(start, end + 1))
                temp_day = end + 1
        
        if not valid:
            continue
        
        # Combine fixed and temp itineraries
        combined_itinerary = itinerary + temp_itinerary
        combined_itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        # Check flight connections
        flight_valid = True
        for i in range(len(combined_itinerary) - 1):
            current_city = combined_itinerary[i]['place']
            next_city = combined_itinerary[i+1]['place']
            if next_city not in flight_graph.get(current_city, []):
                flight_valid = False
                break
        
        if not flight_valid:
            continue
        
        # Calculate score (lower is better)
        score = sum(1 for day in range(1, 22) if day not in fixed_days)
        if score < best_score:
            best_score = score
            best_itinerary = combined_itinerary
    
    if best_itinerary:
        # Ensure all days are covered
        covered_days = set()
        for entry in best_itinerary:
            start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
            covered_days.update(range(start, end + 1))
        
        if len(covered_days) == 21:
            print(json.dumps({'itinerary': best_itinerary}))
        else:
            print(json.dumps({'error': 'No valid itinerary found'}))
    else:
        print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == "__main__":
    main()