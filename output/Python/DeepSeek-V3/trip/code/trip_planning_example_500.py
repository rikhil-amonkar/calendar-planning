import json

def calculate_itinerary():
    # Input parameters
    total_days = 20
    city_days = {
        'Hamburg': 7,
        'Munich': 6,
        'Manchester': 2,
        'Lyon': 2,
        'Split': 7
    }
    
    # Constraints
    manchester_constraint = {'day_range': (19, 20), 'place': 'Manchester'}
    lyon_constraint = {'day_range': (13, 14), 'place': 'Lyon'}
    
    # Direct flights
    direct_flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg', 'Manchester'],
        'Munich': ['Split', 'Manchester', 'Hamburg', 'Lyon'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Assign constrained days first
    days_allocated = [False] * (total_days + 1)  # 1-based indexing
    
    # Assign Manchester constraint (days 19-20)
    for day in range(manchester_constraint['day_range'][0], manchester_constraint['day_range'][1] + 1):
        days_allocated[day] = True
    
    # Assign Lyon constraint (days 13-14)
    for day in range(lyon_constraint['day_range'][0], lyon_constraint['day_range'][1] + 1):
        days_allocated[day] = True
    
    # Assign remaining days to cities
    remaining_city_days = city_days.copy()
    remaining_city_days['Manchester'] -= 2  # already allocated 2 days
    remaining_city_days['Lyon'] -= 2  # already allocated 2 days
    
    # Function to find available days for a city
    def find_available_days(city, required_days):
        available_ranges = []
        start = None
        consecutive = 0
        
        for day in range(1, total_days + 1):
            if not days_allocated[day]:
                if start is None:
                    start = day
                consecutive += 1
                if consecutive == required_days:
                    available_ranges.append((start, day))
                    start = None
                    consecutive = 0
            else:
                start = None
                consecutive = 0
        
        return available_ranges
    
    # Assign Split first (7 days is the largest remaining block)
    split_ranges = find_available_days('Split', remaining_city_days['Split'])
    if not split_ranges:
        return {"error": "Cannot allocate Split days"}
    
    # Choose the earliest possible range for Split
    split_start, split_end = split_ranges[0]
    for day in range(split_start, split_end + 1):
        days_allocated[day] = True
    itinerary.append({'day_range': f'Day {split_start}-{split_end}', 'place': 'Split'})
    remaining_city_days['Split'] = 0
    
    # Assign Hamburg next (7 days)
    hamburg_ranges = find_available_days('Hamburg', remaining_city_days['Hamburg'])
    if not hamburg_ranges:
        return {"error": "Cannot allocate Hamburg days"}
    
    # Choose range that allows flight from Split
    for range_ in hamburg_ranges:
        start, end = range_
        # Check if there's a flight from Split to Hamburg
        if 'Hamburg' in direct_flights['Split']:
            # Add flight from Split to Hamburg
            itinerary.append({'flying': f'Day {split_end}-{split_end}', 'from': 'Split', 'to': 'Hamburg'})
            # Add Hamburg stay
            itinerary.append({'day_range': f'Day {start}-{end}', 'place': 'Hamburg'})
            for day in range(start, end + 1):
                days_allocated[day] = True
            remaining_city_days['Hamburg'] = 0
            break
    
    # Assign Munich next (6 days)
    munich_ranges = find_available_days('Munich', remaining_city_days['Munich'])
    if not munich_ranges:
        return {"error": "Cannot allocate Munich days"}
    
    # Choose range that allows flight from Hamburg
    for range_ in munich_ranges:
        start, end = range_
        if 'Munich' in direct_flights['Hamburg']:
            # Add flight from Hamburg to Munich
            itinerary.append({'flying': f'Day {end_prev}-{end_prev}', 'from': 'Hamburg', 'to': 'Munich'})
            # Add Munich stay
            itinerary.append({'day_range': f'Day {start}-{end}', 'place': 'Munich'})
            for day in range(start, end + 1):
                days_allocated[day] = True
            remaining_city_days['Munich'] = 0
            end_prev = end
            break
    
    # Assign Lyon (already constrained days 13-14)
    # Check if we need to add flight to Lyon
    # Find previous city before Lyon
    prev_city = None
    for entry in reversed(itinerary):
        if 'place' in entry:
            prev_city = entry['place']
            break
    
    if prev_city and 'Lyon' in direct_flights[prev_city]:
        # Add flight to Lyon
        itinerary.append({'flying': f'Day {lyon_constraint["day_range"][0]-1}-{lyon_constraint["day_range"][0]-1}', 
                         'from': prev_city, 'to': 'Lyon'})
    itinerary.append({'day_range': f'Day {lyon_constraint["day_range"][0]}-{lyon_constraint["day_range"][1]}', 'place': 'Lyon'})
    
    # Assign Manchester (already constrained days 19-20)
    # Find previous city before Manchester
    prev_city = None
    for entry in reversed(itinerary):
        if 'place' in entry:
            prev_city = entry['place']
            break
    
    if prev_city and 'Manchester' in direct_flights[prev_city]:
        # Add flight to Manchester
        itinerary.append({'flying': f'Day {manchester_constraint["day_range"][0]-1}-{manchester_constraint["day_range"][0]-1}', 
                         'from': prev_city, 'to': 'Manchester'})
    itinerary.append({'day_range': f'Day {manchester_constraint["day_range"][0]}-{manchester_constraint["day_range"][1]}', 'place': 'Manchester'})
    
    return itinerary

# Calculate and print itinerary
itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))