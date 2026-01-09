import json
from itertools import permutations

def solve_itinerary():
    # Define cities and their required days
    cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]
    required_days = {
        "Hamburg": 7,
        "Munich": 6, 
        "Manchester": 2,
        "Lyon": 2,
        "Split": 7
    }
    
    # Define direct flight connections (bidirectional)
    connections = {
        "Split": ["Munich", "Lyon", "Hamburg", "Manchester"],
        "Munich": ["Split", "Manchester", "Hamburg", "Lyon"],
        "Manchester": ["Munich", "Hamburg", "Split"],
        "Hamburg": ["Manchester", "Munich", "Split"],
        "Lyon": ["Split", "Munich"]
    }
    
    total_days = 20
    
    # Try all possible permutations of cities
    for city_order in permutations(cities):
        valid = True
        
        # Check flight connections between consecutive cities
        for i in range(len(city_order) - 1):
            if city_order[i+1] not in connections[city_order[i]]:
                valid = False
                break
        
        if not valid:
            continue
            
        # Calculate day ranges
        itinerary = []
        current_day = 1
        
        for city in city_order:
            days = required_days[city]
            end_day = current_day + days - 1
            
            if end_day > total_days:
                valid = False
                break
                
            day_range = f"Day {current_day}-{end_day}" if days > 1 else f"Day {current_day}"
            itinerary.append({
                "day_range": day_range,
                "place": city
            })
            
            current_day = end_day + 1
        
        # Check if we used exactly 20 days
        if not valid or current_day != total_days + 1:
            continue
            
        # Check special constraints
        manchester_valid = False
        lyon_valid = False
        
        for item in itinerary:
            if item["place"] == "Manchester":
                # Extract day numbers from day_range
                day_range = item["day_range"]
                if "Day" in day_range:
                    parts = day_range.replace("Day ", "").split("-")
                    start_day = int(parts[0])
                    end_day = int(parts[1]) if len(parts) > 1 else start_day
                    if start_day <= 19 and end_day >= 20:
                        manchester_valid = True
            
            if item["place"] == "Lyon":
                # Extract day numbers from day_range
                day_range = item["day_range"]
                if "Day" in day_range:
                    parts = day_range.replace("Day ", "").split("-")
                    start_day = int(parts[0])
                    end_day = int(parts[1]) if len(parts) > 1 else start_day
                    if start_day <= 13 and end_day >= 14:
                        lyon_valid = True
        
        if manchester_valid and lyon_valid:
            return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found"}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))