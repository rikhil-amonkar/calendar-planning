import json

def find_itinerary():
    cities = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5  # Fixed spelling to match flight connections
    }
    
    direct_flights = {
        'Munich': ['Porto', 'Krakow', 'Milan', 'Split', 'Dubrovnik'],
        'Porto': ['Munich', 'Milan'],
        'Split': ['Milan', 'Krakow', 'Munich'],
        'Milan': ['Split', 'Porto', 'Krakow', 'Munich'],
        'Krakow': ['Munich', 'Split', 'Milan'],
        'Dubrovnik': ['Munich']
    }
    
    # Correct any flight typos
    direct_flights['Split'] = ['Milan', 'Krakow', 'Munich']
    direct_flights['Milan'] = ['Split', 'Porto', 'Krakow', 'Munich']
    direct_flights['Munich'] = direct_flights.pop('Munich')  # Update key spelling
    
    def backtrack(current_itinerary, remaining_cities, current_day, last_city):
        if current_day == 17 and not remaining_cities:
            return current_itinerary
        if current_day > 16:  # We can't exceed 16 days
            return None
            
        for city in list(remaining_cities):
            duration = cities[city]
            end_day = current_day + duration - 1
            
            # Check if this would exceed 16 days
            if end_day > 16:
                continue
                
            # Check special day constraints
            if city == 'Milan' and not (current_day <= 11 <= end_day):
                continue
            if city == 'Krakow' and not (current_day <= 8 <= end_day):
                continue
            if city == 'Munich' and not (current_day <= 4 <= end_day):
                continue
                
            # Check flight connection
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
    
    # Start with Munich since it has the most constrained days (must include day 4)
    remaining_cities = set(cities.keys())
    remaining_cities.remove('Munich')
    
    # Try Munich first (Day 1-5)
    munich_itinerary = [{
        'day_range': "Day 1-5",
        'place': 'Munich'
    }]
    
    result = backtrack(munich_itinerary, remaining_cities, 6, 'Munich')
    if result:
        # Verify total days
        last_day = int(result[-1]['day_range'].split('-')[-1])
        if last_day == 16:
            return {'itinerary': result}
    
    # If Munich-first approach didn't work, try other starting points
    for start_city in cities:
        if start_city == 'Munich':
            continue
            
        remaining_cities = set(cities.keys())
        remaining_cities.remove(start_city)
        
        duration = cities[start_city]
        end_day = duration
        
        # Check if this city can be first (no flight connection needed)
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
            last_day = int(result[-1]['day_range'].split('-')[-1])
            if last_day == 16:
                return {'itinerary': result}
    
    return {'itinerary': []}

def main():
    result = find_itinerary()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()