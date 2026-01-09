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
        # Check if we can travel between consecutive cities in this order
        valid_order = True
        for i in range(len(city_order) - 1):
            if city_order[i+1] not in connections[city_order[i]]:
                valid_order = False
                break
        
        if not valid_order:
            continue
            
        # Calculate day ranges - now accounting for travel days
        itinerary = []
        current_day = 1
        
        for i, city in enumerate(city_order):
            days = required_days[city]
            end_day = current_day + days - 1
            
            if end_day > total_days:
                break
                
            day_range = f"Day {current_day}-{end_day}" if days > 1 else f"Day {current_day}"
            itinerary.append({
                "day_range": day_range,
                "place": city
            })
            
            # Move to next day after this stay (account for travel day)
            current_day = end_day + 1
            
            # If this isn't the last city, we need a travel day
            if i < len(city_order) - 1:
                current_day += 1
        
        # Check if we used exactly 20 days or less
        # We need to account for the fact that we might end before day 20
        last_end_day = 0
        for item in itinerary:
            day_range = item["day_range"]
            parts = day_range.replace("Day ", "").split("-")
            end_day = int(parts[1]) if len(parts) > 1 else int(parts[0])
            last_end_day = max(last_end_day, end_day)
        
        if last_end_day != total_days:
            continue
            
        # Check special constraints
        manchester_valid = False
        lyon_valid = False
        
        for item in itinerary:
            if item["place"] == "Manchester":
                day_range = item["day_range"]
                parts = day_range.replace("Day ", "").split("-")
                start_day = int(parts[0])
                end_day = int(parts[1]) if len(parts) > 1 else start_day
                # Manchester must include Day 19 or 20
                if (start_day <= 19 <= end_day) or (start_day <= 20 <= end_day):
                    manchester_valid = True
            
            if item["place"] == "Lyon":
                day_range = item["day_range"]
                parts = day_range.replace("Day ", "").split("-")
                start_day = int(parts[0])
                end_day = int(parts[1]) if len(parts) > 1 else start_day
                # Lyon must include Day 13 or 14
                if (start_day <= 13 <= end_day) or (start_day <= 14 <= end_day):
                    lyon_valid = True
        
        if manchester_valid and lyon_valid and len(itinerary) == 5:
            return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found"}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))