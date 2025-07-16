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
    
    # Create a list of all days and mark which are already allocated
    day_allocations = [False] * 26  # 1-25
    
    # First, allocate fixed cities
    for city, (start, end) in fixed_cities.items():
        days_needed = cities[city]
        for day in range(start, start + days_needed):
            day_allocations[day] = True
    
    # Backtracking function to find valid itinerary
    def backtrack(current_itinerary, remaining_cities, current_day):
        if current_day > 25:
            if not remaining_cities:
                return current_itinerary
            return None
        
        # If current day is already allocated, skip to next available day
        if day_allocations[current_day]:
            return backtrack(current_itinerary, remaining_cities, current_day + 1)
        
        # Try placing each remaining city that can fit here
        for city in remaining_cities:
            if city in fixed_cities:
                continue
                
            days_needed = cities[city]
            end_day = current_day + days_needed - 1
            if end_day > 25:
                continue
                
            # Check if these days are available
            days_available = True
            for day in range(current_day, end_day + 1):
                if day_allocations[day]:
                    days_available = False
                    break
            if not days_available:
                continue
                
            # Check flight connection if not first city
            if current_itinerary:
                last_city = current_itinerary[-1]['place']
                if city not in flights.get(last_city, []):
                    continue
                    
            # Place the city
            new_itinerary = current_itinerary + [{
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            }]
            
            # Mark days as allocated
            for day in range(current_day, end_day + 1):
                day_allocations[day] = True
                
            new_remaining = remaining_cities - {city}
            result = backtrack(new_itinerary, new_remaining, end_day + 1)
            if result:
                return result
                
            # Backtrack
            for day in range(current_day, end_day + 1):
                day_allocations[day] = False
                
        # Try skipping this day
        return backtrack(current_itinerary, remaining_cities, current_day + 1)
    
    # Start with all cities except fixed ones
    all_cities = set(cities.keys())
    fixed_city_set = set(fixed_cities.keys())
    remaining_cities = all_cities - fixed_city_set
    
    # Add fixed cities to itinerary first
    initial_itinerary = []
    for city in fixed_cities:
        start = fixed_cities[city][0]
        days = cities[city]
        initial_itinerary.append({
            'day_range': f'Day {start}-{start + days - 1}',
            'place': city
        })
    
    # Sort initial itinerary by start day
    initial_itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0][4:]))
    
    itinerary = backtrack(initial_itinerary, remaining_cities, 1)
    
    if itinerary:
        # Verify total days
        total_days = 0
        for entry in itinerary:
            start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
            total_days += end - start + 1
        
        if total_days == 25:
            print(json.dumps({'itinerary': itinerary}))
        else:
            print(json.dumps({'itinerary': []}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()