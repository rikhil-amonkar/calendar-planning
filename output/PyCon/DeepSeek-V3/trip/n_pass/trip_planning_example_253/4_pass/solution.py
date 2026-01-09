import json
from itertools import permutations

def main():
    # Cities and their durations
    cities = {
        'Amsterdam': 3,
        'Vienna': 7, 
        'Santorini': 4,
        'Lyon': 3
    }
    
    # Flight connections (direct flights only)
    connections = {
        'Vienna': ['Lyon', 'Santorini', 'Amsterdam'],
        'Lyon': ['Vienna', 'Amsterdam'],
        'Santorini': ['Vienna', 'Amsterdam'],
        'Amsterdam': ['Vienna', 'Santorini', 'Lyon']
    }
    
    # Try all possible visit orders
    city_names = list(cities.keys())
    
    for visit_order in permutations(city_names):
        # Check flight connections between consecutive cities
        valid_connections = True
        for i in range(len(visit_order) - 1):
            if visit_order[i+1] not in connections[visit_order[i]]:
                valid_connections = False
                break
        
        if not valid_connections:
            continue
            
        # Calculate day ranges
        current_day = 1
        city_days = {}
        
        for city in visit_order:
            duration = cities[city]
            start_day = current_day
            end_day = current_day + duration - 1
            city_days[city] = list(range(start_day, end_day + 1))
            current_day = end_day + 1
        
        # Check total days (must be exactly 14)
        total_used_days = current_day - 1
        if total_used_days != 14:
            continue
            
        # Check workshop constraint: Amsterdam must include at least one day between 9-11
        amsterdam_days = city_days['Amsterdam']
        workshop_valid = any(day in amsterdam_days for day in [9, 10, 11])
        if not workshop_valid:
            continue
            
        # Check wedding constraint: Lyon must include at least one day between 7-9
        lyon_days = city_days['Lyon']
        wedding_valid = any(day in lyon_days for day in [7, 8, 9])
        if not wedding_valid:
            continue
        
        # Found valid itinerary - build the result
        itinerary = []
        current_day = 1
        
        for city in visit_order:
            duration = cities[city]
            end_day = current_day + duration - 1
            
            if duration == 1:
                day_range = f"Day {current_day}"
            else:
                day_range = f"Day {current_day}-{end_day}"
            
            itinerary.append({
                "day_range": day_range,
                "place": city
            })
            
            current_day = end_day + 1
        
        return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found"}

if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))