import json

def find_itinerary():
    cities = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    direct_flights = {
        'Munich': ['Porto', 'Krakow', 'Milan', 'Split', 'Dubrovnik'],
        'Porto': ['Munich', 'Milan'],
        'Split': ['Milan', 'Krakow', 'Munich'],
        'Milan': ['Split', 'Porto', 'Krakow', 'Munich'],
        'Krakow': ['Munich', 'Split', 'Milan'],
        'Dubrovnik': ['Munich']
    }
    
    def backtrack(current_itinerary, remaining_cities, current_day, last_city):
        # Base case: we've reached day 16 and visited all cities
        if current_day == 17 and not remaining_cities:
            return current_itinerary
        if current_day > 16:
            return None
            
        # Try all possible next cities
        for city in list(remaining_cities):
            duration = cities[city]
            end_day = current_day + duration - 1
            
            # Must end exactly on day 16
            if end_day > 16:
                continue
                
            # Check special day constraints
            if city == 'Milan' and not (current_day <= 11 <= end_day):
                continue
            if city == 'Krakow' and not (current_day <= 8 <= end_day):
                continue
            if city == 'Munich' and not (current_day <= 4 <= end_day):
                continue
                
            # Check flight connection (except for first city)
            if last_city and city not in direct_flights.get(last_city, []):
                continue
                
            new_itinerary = current_itinerary + [{
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            }]
            
            result = backtrack(
                new_itinerary,
                remaining_cities - {city},
                end_day + 1,
                city
            )
            
            if result:
                return result
                
        return None
    
    # Try all possible starting cities
    for start_city in cities:
        remaining_cities = set(cities.keys())
        remaining_cities.remove(start_city)
        
        duration = cities[start_city]
        end_day = duration
        
        # Check if this city can be first with its special day requirement
        if start_city == 'Milan' and not (1 <= 11 <= end_day):
            continue
        if start_city == 'Krakow' and not (1 <= 8 <= end_day):
            continue
        if start_city == 'Munich' and not (1 <= 4 <= end_day):
            continue
            
        itinerary_start = [{
            'day_range': f"Day 1-{end_day}",
            'place': start_city
        }]
        
        result = backtrack(
            itinerary_start,
            remaining_cities,
            end_day + 1,
            start_city
        )
        
        if result:
            # Verify the itinerary ends exactly on day 16
            last_day = int(result[-1]['day_range'].split('-')[-1])
            if last_day == 16:
                return {'itinerary': result}
    
    return {'itinerary': []}

def main():
    result = find_itinerary()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()