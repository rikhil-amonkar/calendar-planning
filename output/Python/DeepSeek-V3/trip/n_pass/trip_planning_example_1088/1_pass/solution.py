import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3
    }
    
    # Flight connections (direct flights)
    flights = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Oslo", "Stuttgart", "Split", "Geneva", "Reykjavik"],
        "Stuttgart": ["Porto", "Stockholm", "Split", "Reykjavik"],
        "Oslo": ["Stockholm", "Split", "Geneva", "Porto", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Oslo", "Stockholm", "Geneva"],
        "Geneva": ["Oslo", "Stockholm", "Porto", "Split"],
        "Porto": ["Stuttgart", "Oslo", "Geneva"],
        "Tallinn": ["Oslo", "Reykjavik"]
    }
    
    # Fixed constraints
    fixed_events = [
        ("Reykjavik", 1, 2),  # Conference in Reykjavik on day 1-2
        ("Porto", 19, 21),    # Workshop in Porto on day 19-21
        ("Stockholm", 2, 4)   # Meet friend in Stockholm on day 2-4
    ]
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    best_itinerary = None
    best_score = float('inf')  # Lower score is better (fewer constraint violations)
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Reykjavik is first (due to day 1-2 constraint)
        if order[0] != "Reykjavik":
            continue
        
        # Assign days to cities in order
        temp_itinerary = []
        remaining_days = cities.copy()
        
        for city in order:
            days_needed = remaining_days[city]
            
            # Check if city is Porto and must be at the end
            if city == "Porto":
                if current_day + days_needed - 1 > 21 or current_day > 19:
                    valid = False
                    break
                end_day = current_day + days_needed - 1
                if end_day < 19:
                    valid = False
                    break
            
            # Check if city is Stockholm and must be between day 2-4
            if city == "Stockholm":
                start_day = current_day
                end_day = current_day + days_needed - 1
                if not (start_day <= 4 and end_day >= 2):
                    valid = False
                    break
            
            # Assign days
            end_day = current_day + days_needed - 1
            if end_day > 21:
                valid = False
                break
            
            temp_itinerary.append((city, current_day, end_day))
            current_day = end_day + 1
        
        if not valid:
            continue
        
        # Check all fixed events
        for event_city, start, end in fixed_events:
            found = False
            for (city, s, e) in temp_itinerary:
                if city == event_city and s <= end and e >= start:
                    found = True
                    break
            if not found:
                valid = False
                break
        
        if not valid:
            continue
        
        # Check flight connections between cities
        for i in range(len(order) - 1):
            current_city = order[i]
            next_city = order[i+1]
            if next_city not in flights[current_city]:
                valid = False
                break
        
        if not valid:
            continue
        
        # Calculate score (total days used, prefer closer to 21)
        total_days = sum([e - s + 1 for (_, s, e) in temp_itinerary])
        score = abs(total_days - 21)
        
        if score < best_score:
            best_score = score
            best_itinerary = temp_itinerary
    
    if best_itinerary is None:
        return {"itinerary": []}
    
    # Format the itinerary
    formatted_itinerary = []
    for city, start, end in best_itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        formatted_itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": formatted_itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))