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
    
    # Initialize schedule with fixed events
    schedule = [None] * 21  # 0-based index for days 1-21
    for city, start, end in fixed_events:
        for day in range(start-1, end):
            schedule[day] = city
    
    # Remaining cities to visit (excluding fixed events)
    remaining_cities = [city for city in cities.keys() if city not in {x[0] for x in fixed_events}]
    remaining_days = {city: cities[city] for city in remaining_cities}
    
    # Find available blocks of days
    available_blocks = []
    current_block = None
    for day in range(21):
        if schedule[day] is None:
            if current_block is None:
                current_block = [day, day]  # 0-based start and end
            else:
                current_block[1] = day
        else:
            if current_block is not None:
                available_blocks.append(current_block)
                current_block = None
    if current_block is not None:
        available_blocks.append(current_block)
    
    # Sort blocks by size (descending)
    available_blocks.sort(key=lambda x: x[1]-x[0], reverse=True)
    
    # Sort cities by required days (descending)
    remaining_cities_sorted = sorted(remaining_cities, key=lambda x: remaining_days[x], reverse=True)
    
    # Try to assign cities to blocks
    city_index = 0
    for city in remaining_cities_sorted:
        days_needed = remaining_days[city]
        assigned = False
        
        # Try to find a suitable block
        for i, block in enumerate(available_blocks):
            block_size = block[1] - block[0] + 1
            if block_size >= days_needed:
                # Assign city to this block
                for day in range(block[0], block[0] + days_needed):
                    schedule[day] = city
                
                # Update the block (remaining days)
                if block_size > days_needed:
                    new_block = [block[0] + days_needed, block[1]]
                    available_blocks[i] = new_block
                else:
                    available_blocks.pop(i)
                
                assigned = True
                break
        
        if not assigned:
            # Couldn't assign this city - try to split days
            for i, block in enumerate(available_blocks):
                if block[1] - block[0] + 1 > 0:
                    # Assign as many days as possible
                    days_to_assign = min(block[1] - block[0] + 1, days_needed)
                    for day in range(block[0], block[0] + days_to_assign):
                        schedule[day] = city
                    
                    # Update remaining days needed
                    remaining_days[city] -= days_to_assign
                    
                    # Update the block
                    if block[1] - block[0] + 1 > days_to_assign:
                        new_block = [block[0] + days_to_assign, block[1]]
                        available_blocks[i] = new_block
                    else:
                        available_blocks.pop(i)
                    
                    if remaining_days[city] == 0:
                        assigned = True
                        break
    
    # Verify all days are filled
    if None in schedule:
        return {"itinerary": []}
    
    # Verify all cities got their required days
    for city in remaining_cities_sorted:
        if sum(1 for day in schedule if day == city) < cities[city]:
            return {"itinerary": []}
    
    # Verify flight connections
    current_city = schedule[0]
    for day in range(1, 21):
        next_city = schedule[day]
        if next_city != current_city:
            if next_city not in flights.get(current_city, []):
                return {"itinerary": []}
            current_city = next_city
    
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

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))