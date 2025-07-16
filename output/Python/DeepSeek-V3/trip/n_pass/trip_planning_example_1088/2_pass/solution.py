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
    
    for order in possible_orders:
        # Must start with Reykjavik
        if order[0] != "Reykjavik":
            continue
            
        # Must include Porto in the last position
        if order[-1] != "Porto":
            continue
            
        # Initialize itinerary
        itinerary = []
        days_used = 0
        
        # Check flight connections
        valid_flights = True
        for i in range(len(order)-1):
            if order[i+1] not in flights[order[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue
            
        # Assign days while respecting fixed events
        current_day = 1
        temp_itinerary = []
        
        for city in order:
            days_needed = cities[city]
            end_day = current_day + days_needed - 1
            
            # Check if this assignment would exceed 21 days
            if end_day > 21:
                break
                
            # Check fixed events for this city
            for event_city, event_start, event_end in fixed_events:
                if city == event_city:
                    # Must fully contain the fixed event
                    if not (current_day <= event_start and end_day >= event_end):
                        break
            else:  # No break in for loop
                temp_itinerary.append((city, current_day, end_day))
                current_day = end_day + 1
                continue
            break  # Break if fixed event check failed
        else:  # No break in for loop (all cities assigned)
            # Check if we've used exactly 21 days
            if current_day - 1 == 21:
                best_itinerary = temp_itinerary
                break  # Found perfect itinerary
    
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