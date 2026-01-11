import json
from itertools import permutations

def find_valid_itinerary():
    # City durations from the problem
    city_durations = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    # Direct flight connections (undirected)
    connections = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Reykjavik': ['Helsinki', 'Prague'],
        'Dubrovnik': ['Helsinki']
    }
    
    # Check all permutations of city order
    cities = list(city_durations.keys())
    
    for perm in permutations(cities):
        # Check if consecutive cities are connected by direct flights
        valid_route = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in connections[perm[i]]:
                valid_route = False
                break
        
        if not valid_route:
            continue
            
        # Now check if we can schedule days to meet Porto constraint
        # Porto must be between days 16-18 (inclusive)
        # Since Porto requires 3 days, it must occupy days 16, 17, 18
        
        # Generate all possible day assignments
        # We need to assign start days to each city in order
        
        def try_schedule(order):
            # Try to assign start days to each city
            # Total days: 18
            positions = [0] * len(order)  # Start day for each city (0-indexed)
            current_day = 0
            
            for i, city in enumerate(order):
                positions[i] = current_day
                current_day += city_durations[city]
            
            # Check if total days = 18
            if current_day != 18:
                return None
            
            # Check Porto constraint
            porto_index = order.index('Porto')
            porto_start = positions[porto_index]
            porto_end = porto_start + city_durations['Porto'] - 1
            
            # Porto must end on day 18 (0-indexed: day 17)
            # So porto_end must be 17, which means porto_start must be 15
            # This means Porto occupies days 16, 17, 18 (1-indexed)
            if porto_end != 17:  # 0-indexed: day 17 = 1-indexed: day 18
                return None
            
            # Convert to 1-indexed days for output
            schedule = []
            for i, city in enumerate(order):
                start_day = positions[i] + 1  # Convert to 1-indexed
                end_day = start_day + city_durations[city] - 1
                day_range = f"Day {start_day}-{end_day}"
                schedule.append({"day_range": day_range, "place": city})
            
            return schedule
        
        schedule = try_schedule(perm)
        if schedule:
            return schedule
    
    return None

def main():
    # Find a valid itinerary
    itinerary = find_valid_itinerary()
    
    if itinerary:
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": [], "error": "No valid itinerary found"}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()