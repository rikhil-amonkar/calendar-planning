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
    
    for order in possible_orders:
        # Must start with Reykjavik
        if order[0] != "Reykjavik":
            continue
            
        # Must include Porto in the last position
        if order[-1] != "Porto":
            continue
            
        # Check flight connections
        valid_flights = True
        for i in range(len(order)-1):
            if order[i+1] not in flights[order[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue
            
        # Initialize schedule
        schedule = [None] * 21  # 0-based index for days 1-21
        
        # Assign fixed events first
        conflict = False
        for city, start, end in fixed_events:
            for day in range(start-1, end):
                if schedule[day] is not None:
                    conflict = True
                    break
                schedule[day] = city
            if conflict:
                break
        if conflict:
            continue
            
        # Get remaining cities and their required days
        remaining_cities = [city for city in order if city not in {x[0] for x in fixed_events}]
        remaining_days = {city: cities[city] for city in remaining_cities}
        
        # Find available blocks
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
        
        # Try to assign remaining cities to available blocks
        city_index = 0
        for block in available_blocks:
            if city_index >= len(remaining_cities):
                break
            current_city = remaining_cities[city_index]
            days_needed = remaining_days[current_city]
            block_size = block[1] - block[0] + 1
            
            if block_size >= days_needed:
                # Assign city to this block
                start_day = block[0] + 1  # Convert to 1-based
                end_day = start_day + days_needed - 1
                for day in range(block[0], block[0] + days_needed):
                    schedule[day] = current_city
                city_index += 1
            else:
                # Try to find another block that fits
                continue
        
        # Check if all cities were assigned
        if city_index != len(remaining_cities):
            continue
            
        # Check if all days are filled
        if None in schedule:
            continue
            
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