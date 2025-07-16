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
        temp_itinerary = []
        days_used = 0
        
        # Check flight connections
        valid_flights = True
        for i in range(len(order)-1):
            if order[i+1] not in flights[order[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue
            
        # Create a day schedule
        schedule = [None] * 21  # 1-based indexing (days 1-21)
        
        # First assign fixed events
        for city, start, end in fixed_events:
            for day in range(start-1, end):  # Convert to 0-based index
                if schedule[day] is not None:
                    break  # Conflict found
            else:
                for day in range(start-1, end):
                    schedule[day] = city
                continue
            break  # Conflict found, skip this order
        else:  # All fixed events assigned successfully
            # Now assign remaining cities and days
            remaining_cities = [city for city in order if city not in {x[0] for x in fixed_events}]
            
            # Find available blocks for remaining cities
            available_blocks = []
            current_block = None
            for day in range(21):
                if schedule[day] is None:
                    if current_block is None:
                        current_block = [day+1, day+1]  # 1-based start and end
                    else:
                        current_block[1] = day+1
                else:
                    if current_block is not None:
                        available_blocks.append(current_block)
                        current_block = None
            if current_block is not None:
                available_blocks.append(current_block)
            
            # Assign remaining cities to available blocks
            if len(remaining_cities) > len(available_blocks):
                continue  # Not enough blocks for cities
                
            # Try to assign cities to blocks
            city_index = 0
            valid_assignment = True
            for block in available_blocks:
                if city_index >= len(remaining_cities):
                    break
                city = remaining_cities[city_index]
                days_needed = cities[city]
                block_size = block[1] - block[0] + 1
                
                if block_size >= days_needed:
                    # Assign city to this block
                    start = block[0]
                    end = start + days_needed - 1
                    for day in range(start-1, end):
                        schedule[day] = city
                    temp_itinerary.append((city, start, end))
                    city_index += 1
                else:
                    # Try to split city across blocks (not allowed)
                    valid_assignment = False
                    break
            
            if valid_assignment and city_index == len(remaining_cities):
                # Verify all days are filled
                if None not in schedule:
                    # Format the itinerary
                    formatted_itinerary = []
                    current_city = schedule[0]
                    start_day = 1
                    for day in range(1, 21):
                        if schedule[day] != current_city:
                            formatted_itinerary.append({
                                "day_range": f"Day {start_day}-{day}" if start_day != day else f"Day {start_day}",
                                "place": current_city
                            })
                            current_city = schedule[day]
                            start_day = day + 1
                    # Add last city
                    formatted_itinerary.append({
                        "day_range": f"Day {start_day}-21" if start_day != 21 else f"Day 21",
                        "place": current_city
                    })
                    return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))