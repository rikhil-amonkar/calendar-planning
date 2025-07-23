import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 12
    city_days = {
        'Frankfurt': 3,
        'Naples': 4,
        'Helsinki': 4,
        'Lyon': 3,
        'Prague': 2
    }
    
    # Special constraints
    helsinki_show = (2, 5)  # Day 2 to Day 5 must be in Helsinki
    prague_workshop = (1, 2)  # Must be in Prague between Day 1 and Day 2
    
    # Direct flights
    direct_flights = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }
    
    # All cities
    cities = list(city_days.keys())
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # Check if the permutation can satisfy the constraints
        itinerary = []
        current_day = 1
        prev_city = None
        
        # Check Helsinki show constraint
        helsinki_start = helsinki_show[0]
        helsinki_end = helsinki_show[1]
        if 'Helsinki' not in perm:
            continue
        
        # Check Prague workshop constraint
        prague_start = prague_workshop[0]
        prague_end = prague_workshop[1]
        if 'Prague' not in perm:
            continue
        
        # Try to build the itinerary
        temp_itinerary = []
        remaining_days = city_days.copy()
        day = 1
        
        # First, handle Prague workshop (must be in Prague on day 1-2)
        if day <= prague_end:
            days_in_prague = min(prague_end - day + 1, remaining_days['Prague'])
            if days_in_prague <= 0:
                continue
            temp_itinerary.append({'day_range': f'Day {day}-{day + days_in_prague - 1}', 'place': 'Prague'})
            day += days_in_prague
            remaining_days['Prague'] -= days_in_prague
        
        # Next, handle Helsinki show (must be in Helsinki on day 2-5)
        if day <= helsinki_end:
            days_in_helsinki = min(helsinki_end - day + 1, remaining_days['Helsinki'])
            if days_in_helsinki <= 0:
                continue
            temp_itinerary.append({'day_range': f'Day {day}-{day + days_in_helsinki - 1}', 'place': 'Helsinki'})
            day += days_in_helsinki
            remaining_days['Helsinki'] -= days_in_helsinki
        
        # Now, assign remaining days to other cities
        for city in perm:
            if city == 'Prague' or city == 'Helsinki':
                continue
            if remaining_days[city] > 0:
                if day > total_days:
                    break
                # Check if we can fly from previous city to this city
                prev_place = temp_itinerary[-1]['place'] if temp_itinerary else None
                if prev_place and city not in direct_flights[prev_place]:
                    break
                days_in_city = min(remaining_days[city], total_days - day + 1)
                if days_in_city <= 0:
                    continue
                temp_itinerary.append({'day_range': f'Day {day}-{day + days_in_city - 1}', 'place': city})
                day += days_in_city
                remaining_days[city] -= days_in_city
        
        # Assign remaining days to Helsinki or Prague if needed
        for city in ['Helsinki', 'Prague']:
            if remaining_days[city] > 0:
                if day > total_days:
                    break
                prev_place = temp_itinerary[-1]['place'] if temp_itinerary else None
                if prev_place and city not in direct_flights[prev_place]:
                    break
                days_in_city = min(remaining_days[city], total_days - day + 1)
                if days_in_city <= 0:
                    continue
                temp_itinerary.append({'day_range': f'Day {day}-{day + days_in_city - 1}', 'place': city})
                day += days_in_city
                remaining_days[city] -= days_in_city
        
        # Check if all days are assigned and all city days are satisfied
        if day > total_days and all(v == 0 for v in remaining_days.values()):
            # Verify flight connections
            valid = True
            for i in range(1, len(temp_itinerary)):
                prev_city = temp_itinerary[i-1]['place']
                current_city = temp_itinerary[i]['place']
                if current_city not in direct_flights[prev_city]:
                    valid = False
                    break
            if valid:
                return {'itinerary': temp_itinerary}
    
    # If no valid itinerary found, return an empty list
    return {'itinerary': []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result))