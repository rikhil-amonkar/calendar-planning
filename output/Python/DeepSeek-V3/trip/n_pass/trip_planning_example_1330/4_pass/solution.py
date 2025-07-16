import json

def main():
    # Define the cities and their required days
    cities = {
        'Salzburg': 2,
        'Venice': 5,
        'Bucharest': 4,
        'Brussels': 2,
        'Hamburg': 4,
        'Copenhagen': 4,
        'Nice': 3,
        'Zurich': 5,
        'Naples': 4
    }
    
    # Define the flight connections
    flights = {
        'Zurich': ['Brussels', 'Nice', 'Naples', 'Copenhagen', 'Venice', 'Bucharest', 'Hamburg'],
        'Brussels': ['Zurich', 'Venice', 'Bucharest', 'Hamburg', 'Nice', 'Copenhagen', 'Naples'],
        'Bucharest': ['Copenhagen', 'Hamburg', 'Brussels', 'Naples', 'Zurich'],
        'Venice': ['Brussels', 'Naples', 'Copenhagen', 'Zurich', 'Nice', 'Hamburg'],
        'Nice': ['Zurich', 'Hamburg', 'Venice', 'Brussels', 'Naples', 'Copenhagen'],
        'Hamburg': ['Nice', 'Bucharest', 'Brussels', 'Zurich', 'Copenhagen', 'Venice', 'Salzburg'],
        'Copenhagen': ['Bucharest', 'Venice', 'Zurich', 'Hamburg', 'Brussels', 'Naples', 'Nice'],
        'Naples': ['Zurich', 'Venice', 'Bucharest', 'Brussels', 'Copenhagen', 'Nice'],
        'Salzburg': ['Hamburg']
    }
    
    # Fixed constraints
    fixed_cities = {
        'Brussels': (21, 22),
        'Copenhagen': (18, 21),
        'Nice': (9, 11),
        'Naples': (22, 25)
    }
    
    # Backtracking function to find valid itinerary
    def backtrack(current_itinerary, remaining_cities, current_day, used_days):
        if used_days == 25 and not remaining_cities:
            return current_itinerary
        
        # Try to place fixed cities first if we're at their start day
        for city, (start, end) in fixed_cities.items():
            if city in remaining_cities and current_day == start:
                days_needed = cities[city]
                # Check if this fits in the fixed window
                if start + days_needed - 1 > end:
                    return None
                
                # Check flight connection if not first city
                if current_itinerary:
                    last_city = current_itinerary[-1]['place']
                    if city not in flights.get(last_city, []):
                        return None
                
                new_itinerary = current_itinerary + [{
                    'day_range': f'Day {start}-{start + days_needed - 1}',
                    'place': city
                }]
                new_remaining = remaining_cities - {city}
                result = backtrack(new_itinerary, new_remaining, start + days_needed, used_days + days_needed)
                if result:
                    return result
                return None
        
        # Try other cities if no fixed city needs to be placed now
        for city in remaining_cities:
            if city in fixed_cities:
                continue
                
            days_needed = cities[city]
            end_day = current_day + days_needed - 1
            if end_day > 25:
                continue
                
            # Check if this overlaps with any fixed city's window
            conflict = False
            for fixed_city, (start, end) in fixed_cities.items():
                if fixed_city in remaining_cities:
                    continue
                if (current_day <= end) and (end_day >= start):
                    conflict = True
                    break
            if conflict:
                continue
                
            # Check flight connection if not first city
            if current_itinerary:
                last_city = current_itinerary[-1]['place']
                if city not in flights.get(last_city, []):
                    continue
                    
            new_itinerary = current_itinerary + [{
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            }]
            new_remaining = remaining_cities - {city}
            result = backtrack(new_itinerary, new_remaining, end_day + 1, used_days + days_needed)
            if result:
                return result
                
        return None
    
    # Start with all cities remaining
    all_cities = set(cities.keys())
    itinerary = backtrack([], all_cities, 1, 0)
    
    if itinerary:
        print(json.dumps({'itinerary': itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()