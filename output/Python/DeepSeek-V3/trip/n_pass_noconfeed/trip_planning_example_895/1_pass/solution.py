import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Venice': 3,
        'London': 3,
        'Lisbon': 4,
        'Brussels': 2,
        'Reykjavik': 3,
        'Santorini': 3,
        'Madrid': 5
    }
    
    # Direct flights
    flights = {
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Santorini', 'Lisbon', 'Brussels'],
        'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid', 'Brussels'],
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice']
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Brussels', 1, 2),
        ('Venice', 5, 7),
        ('Madrid', 7, 11)
    ]
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    
    # We'll try all possible permutations (though this is computationally expensive for larger numbers)
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check fixed constraints first
        for city, start, end in fixed_constraints:
            if city not in perm:
                valid = False
                break
        
        if not valid:
            continue
        
        # Try to build itinerary based on permutation
        temp_itinerary = []
        prev_city = None
        
        # Assign fixed days first
        days_assigned = [False] * 18  # 1-based index up to day 17
        
        # Mark Brussels days 1-2
        for day in range(1, 3):
            days_assigned[day] = True
        temp_itinerary.append({'day_range': f'Day 1-2', 'place': 'Brussels'})
        prev_city = 'Brussels'
        current_day = 3
        
        # Assign Venice days 5-7
        for day in range(5, 8):
            if day > 17:
                valid = False
                break
            days_assigned[day] = True
        if valid:
            temp_itinerary.append({'day_range': f'Day 5-7', 'place': 'Venice'})
        
        # Assign Madrid days 7-11
        for day in range(7, 12):
            if day > 17:
                valid = False
                break
            days_assigned[day] = True
        if valid:
            temp_itinerary.append({'day_range': f'Day 7-11', 'place': 'Madrid'})
        
        if not valid:
            continue
        
        # Now assign remaining cities and days
        remaining_cities = [city for city in perm if city not in ['Brussels', 'Venice', 'Madrid']]
        remaining_days = cities.copy()
        remaining_days['Brussels'] -= 2
        remaining_days['Venice'] -= 3
        remaining_days['Madrid'] -= 5
        
        # We need to assign:
        # London: 3 days
        # Lisbon: 4 days
        # Reykjavik: 3 days
        # Santorini: 3 days
        
        # Try to assign these in the remaining days (3-4, 8-17)
        # This is complex, so we'll use a greedy approach
        
        # We'll try to assign the remaining cities in the permutation order
        current_city_index = 0
        current_day = 3
        
        while current_day <= 17 and current_city_index < len(remaining_cities):
            city = remaining_cities[current_city_index]
            if remaining_days[city] <= 0:
                current_city_index += 1
                continue
            
            # Check if we can fly from previous city
            if prev_city and city not in flights[prev_city]:
                valid = False
                break
            
            # Assign as many days as possible
            start_day = current_day
            end_day = start_day + remaining_days[city] - 1
            
            # Check if these days are available
            all_available = True
            for day in range(start_day, end_day + 1):
                if day > 17 or days_assigned[day]:
                    all_available = False
                    break
            
            if all_available:
                for day in range(start_day, end_day + 1):
                    days_assigned[day] = True
                temp_itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                prev_city = city
                current_day = end_day + 1
                remaining_days[city] = 0
                current_city_index += 1
            else:
                # Try to assign partial days
                days_to_assign = 0
                for day in range(current_day, 18):
                    if not days_assigned[day]:
                        days_to_assign += 1
                        if days_to_assign == remaining_days[city]:
                            break
                
                if days_to_assign >= remaining_days[city]:
                    end_day = current_day + remaining_days[city] - 1
                    for day in range(current_day, end_day + 1):
                        days_assigned[day] = True
                    temp_itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})
                    prev_city = city
                    current_day = end_day + 1
                    remaining_days[city] = 0
                    current_city_index += 1
                else:
                    current_city_index += 1
        
        # Check if all days are assigned correctly
        if valid:
            all_assigned = True
            for city, days in remaining_days.items():
                if days > 0:
                    all_assigned = False
                    break
            
            if all_assigned:
                # Check if all 17 days are covered
                day_coverage = [False] * 18
                for entry in temp_itinerary:
                    start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
                    for day in range(start, end + 1):
                        day_coverage[day] = True
                
                if all(day_coverage[1:18]):
                    # Sort itinerary by day ranges
                    def get_start_day(entry):
                        return int(entry['day_range'].split('Day ')[1].split('-')[0])
                    
                    temp_itinerary.sort(key=get_start_day)
                    return {'itinerary': temp_itinerary}
    
    # If no valid itinerary found (shouldn't happen with correct constraints)
    return {'itinerary': []}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))