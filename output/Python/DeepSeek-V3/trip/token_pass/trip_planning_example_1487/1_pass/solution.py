import json
from itertools import permutations

def find_valid_itinerary():
    # Cities and required days
    cities = {
        'Copenhagen': 5,
        'Geneva': 3,
        'Mykonos': 2,
        'Naples': 4,
        'Prague': 2,
        'Dubrovnik': 3,
        'Athens': 4,
        'Santorini': 5,
        'Brussels': 4,
        'Munich': 5
    }
    
    # Direct flight connections
    direct_flights = {
        'Copenhagen': ['Dubrovnik', 'Brussels', 'Naples', 'Prague', 'Athens', 'Geneva', 'Munich', 'Santorini'],
        'Geneva': ['Prague', 'Athens', 'Mykonos', 'Naples', 'Munich', 'Brussels', 'Copenhagen', 'Dubrovnik', 'Santorini'],
        'Mykonos': ['Geneva', 'Naples', 'Munich', 'Athens'],
        'Naples': ['Dubrovnik', 'Mykonos', 'Copenhagen', 'Athens', 'Munich', 'Geneva', 'Santorini', 'Brussels'],
        'Prague': ['Geneva', 'Athens', 'Copenhagen', 'Brussels', 'Munich'],
        'Dubrovnik': ['Copenhagen', 'Naples', 'Athens', 'Munich', 'Geneva'],
        'Athens': ['Geneva', 'Dubrovnik', 'Naples', 'Prague', 'Santorini', 'Mykonos', 'Copenhagen', 'Brussels', 'Munich'],
        'Santorini': ['Geneva', 'Athens', 'Copenhagen', 'Naples'],
        'Brussels': ['Copenhagen', 'Naples', 'Prague', 'Athens', 'Munich', 'Geneva'],
        'Munich': ['Mykonos', 'Naples', 'Dubrovnik', 'Brussels', 'Athens', 'Geneva', 'Copenhagen', 'Prague']
    }
    
    # Time constraints
    constraints = {
        'Copenhagen': {'min_day': 11, 'max_day': 15, 'duration': 5},
        'Mykonos': {'fixed_days': [27, 28], 'duration': 2},
        'Naples': {'min_day': 5, 'max_day': 8, 'duration': 4},
        'Athens': {'min_day': 8, 'max_day': 11, 'duration': 4}
    }
    
    # Try different city orders
    city_list = list(cities.keys())
    
    # We'll use a backtracking approach to find a valid schedule
    def backtrack(schedule, current_day, remaining_cities, used_days):
        if current_day > 28:
            return schedule if len(schedule) == 10 and sum(used_days.values()) == 28 else None
        
        if len(schedule) == 10:
            # Check if all days are used
            total_days = sum(used_days.values())
            if total_days == 28:
                return schedule
            return None
        
        for city in remaining_cities:
            # Check if we can place this city starting at current_day
            duration = cities[city]
            
            # Check constraints
            if city in constraints:
                const = constraints[city]
                if 'fixed_days' in const:
                    # Mykonos must be on days 27-28
                    if city == 'Mykonos':
                        if current_day != 27:
                            continue
                        duration = 2
                elif 'min_day' in const:
                    # City must include days in range
                    if current_day > const['min_day'] or (current_day + duration - 1) < const['min_day']:
                        continue
            
            # Check if duration fits within 28 days
            if current_day + duration - 1 > 28:
                continue
            
            # Check flight connection if not first city
            if schedule:
                last_city = schedule[-1]['city']
                if city not in direct_flights[last_city]:
                    continue
            
            # Add city to schedule
            new_schedule = schedule + [{
                'city': city,
                'start_day': current_day,
                'end_day': current_day + duration - 1,
                'duration': duration
            }]
            
            new_used_days = used_days.copy()
            new_used_days[city] = duration
            
            # Try to continue
            result = backtrack(new_schedule, current_day + duration, 
                              [c for c in remaining_cities if c != city], new_used_days)
            if result:
                return result
        
        return None
    
    # Generate all permutations and try to find valid schedule
    for perm in permutations(city_list):
        schedule = backtrack([], 1, list(perm), {})
        if schedule:
            # Verify all constraints are satisfied
            valid = True
            
            # Check specific constraints
            for entry in schedule:
                city = entry['city']
                start = entry['start_day']
                end = entry['end_day']
                
                if city == 'Copenhagen':
                    # Must include days 11-15
                    if not (start <= 15 and end >= 11):
                        valid = False
                        break
                
                if city == 'Mykonos':
                    # Must be on days 27-28
                    if start != 27 or end != 28:
                        valid = False
                        break
                
                if city == 'Naples':
                    # Must include days 5-8
                    if not (start <= 8 and end >= 5):
                        valid = False
                        break
                
                if city == 'Athens':
                    # Must include days 8-11
                    if not (start <= 11 and end >= 8):
                        valid = False
                        break
            
            if valid:
                # Verify flight connections
                for i in range(1, len(schedule)):
                    prev_city = schedule[i-1]['city']
                    curr_city = schedule[i]['city']
                    if curr_city not in direct_flights[prev_city]:
                        valid = False
                        break
                
                if valid:
                    return schedule
    
    return None

def main():
    # Find a valid itinerary
    schedule = find_valid_itinerary()
    
    if not schedule:
        print('{"error": "No valid itinerary found"}')
        return
    
    # Format output
    itinerary = []
    for entry in schedule:
        city = entry['city']
        start = entry['start_day']
        end = entry['end_day']
        
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
    
    # Create output dictionary
    output = {"itinerary": itinerary}
    
    # Print JSON output
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()