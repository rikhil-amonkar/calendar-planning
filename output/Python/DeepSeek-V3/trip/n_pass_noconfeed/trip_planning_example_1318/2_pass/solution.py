import json

def find_itinerary():
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    flight_routes = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Edinburgh': ['Budapest', 'Geneva', 'Porto', 'Oslo', 'Helsinki', 'Riga'],
        'Riga': ['Tallinn', 'Oslo', 'Helsinki', 'Vilnius'],
        'Tallinn': ['Vilnius', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Oslo'],
        'Helsinki': ['Budapest', 'Oslo', 'Geneva'],
        'Budapest': ['Geneva', 'Oslo'],
        'Geneva': ['Oslo', 'Porto'],
        'Oslo': ['Porto', 'Edinburgh', 'Geneva', 'Riga', 'Tallinn', 'Vilnius', 'Budapest', 'Helsinki']
    }
    
    # Constraints
    wedding_in_tallinn = (4, 8)  # Must be in Tallinn between day 4 and day 8
    meet_in_oslo = (24, 25)      # Must be in Oslo between day 24 and day 25
    
    def backtrack(current_itinerary, current_day, visited_cities, last_city):
        # Check if we've used all 25 days
        if current_day > 25:
            return None
        
        # Check if we've completed the itinerary
        if current_day == 25:
            # Check constraints
            tallinn_ok = False
            oslo_ok = False
            
            for visit in current_itinerary:
                city = visit['place']
                start_day = int(visit['day_range'].split('-')[0][4:])
                end_day = int(visit['day_range'].split('-')[1][4:])
                
                if city == 'Tallinn':
                    if start_day <= wedding_in_tallinn[1] and end_day >= wedding_in_tallinn[0]:
                        tallinn_ok = True
                if city == 'Oslo':
                    if start_day <= meet_in_oslo[1] and end_day >= meet_in_oslo[0]:
                        oslo_ok = True
            
            if tallinn_ok and oslo_ok:
                return current_itinerary
            else:
                return None
        
        # Try to add cities that can be reached from the last city
        for city in flight_routes.get(last_city, []):
            if city not in visited_cities:
                duration = cities[city]
                start_day = current_day
                end_day = current_day + duration - 1
                
                # Check if adding this city would exceed 25 days
                if end_day > 25:
                    continue
                
                new_visit = {'day_range': f'Day {start_day}-{end_day}', 'place': city}
                new_itinerary = current_itinerary + [new_visit]
                result = backtrack(new_itinerary, end_day + 1, visited_cities | {city}, city)
                if result:
                    return result
        
        return None
    
    # Try starting from different cities
    for start_city in cities:
        duration = cities[start_city]
        if duration > 25:
            continue
            
        start_day = 1
        end_day = start_day + duration - 1
        initial_visit = {'day_range': f'Day {start_day}-{end_day}', 'place': start_city}
        result = backtrack([initial_visit], end_day + 1, {start_city}, start_city)
        if result:
            return {'itinerary': result}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))