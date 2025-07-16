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
    
    # Correct any flight typos
    direct_flights['Split'] = ['Milan', 'Krakow', 'Munich']
    direct_flights['Milan'] = ['Split', 'Porto', 'Krakow', 'Munich']
    
    def backtrack(current_itinerary, remaining_cities, current_day, last_city):
        if current_day == 17 and not remaining_cities:
            return current_itinerary
        
        if current_day >= 17:
            return None
            
        for city in list(remaining_cities):
            duration = cities[city]
            end_day = current_day + duration - 1
            
            # Check day constraints
            if city == 'Milan' and not (11 >= current_day and 11 <= end_day):
                continue
            if city == 'Krakow' and not (8 >= current_day and 8 <= end_day):
                continue
            if city == 'Munich' and not (4 >= current_day and 4 <= end_day):
                continue
            
            # Check flight connection
            if last_city and city not in direct_flights[last_city]:
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
    
    # Try Munich first
    munich_itinerary = [{
        'day_range': "Day 1-5",
        'place': 'Munich'
    }]
    
    result = backtrack(munich_itinerary, remaining_cities, 6, 'Munich')
    if result:
        return {'itinerary': result}
    
    return {'itinerary': []}

def main():
    result = find_itinerary()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()