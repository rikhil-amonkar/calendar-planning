import json

def create_itinerary():
    # Define the fixed events
    fixed_events = {
        "Reykjavik": (4, 7),  # Wedding
        "Amsterdam": (14, 15),  # Conference
        "Munich": (7, 10)  # Meet a friend
    }
    
    # Define the minimum days required in each city
    min_days_in_city = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }
    
    # Initialize the itinerary list
    itinerary = []
    
    # Add fixed events to the itinerary
    itinerary.append({"day_range": f"Day {fixed_events['Reykjavik'][0]}-{fixed_events['Reykjavik'][1]}", "place": "Reykjavik"})
    itinerary.append({"day_range": f"Day {fixed_events['Amsterdam'][0]}-{fixed_events['Amsterdam'][1]}", "place": "Amsterdam"})
    itinerary.append({"day_range": f"Day {fixed_events['Munich'][0]}-{fixed_events['Munich'][1]}", "place": "Munich"})
    
    # Sort the fixed events by their start day
    fixed_events_sorted = sorted(fixed_events.items(), key=lambda x: x[1][0])
    
    # Calculate remaining days and allocate them to cities
    current_day = 1
    for event, (start, end) in fixed_events_sorted:
        if current_day < start:
            # Allocate days before the fixed event
            days_to_allocate = start - current_day
            for city, min_days in min_days_in_city.items():
                if min_days > 0 and days_to_allocate > 0:
                    days_in_city = min(min_days, days_to_allocate)
                    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_city - 1}", "place": city})
                    min_days_in_city[city] -= days_in_city
                    days_to_allocate -= days_in_city
                    current_day += days_in_city
        # Move to the day after the fixed event
        current_day = end + 1
    
    # Allocate remaining days after the last fixed event
    while current_day <= 16:
        for city, min_days in min_days_in_city.items():
            if min_days > 0:
                days_in_city = min(min_days, 16 - current_day + 1)
                itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_city - 1}", "place": city})
                min_days_in_city[city] -= days_in_city
                current_day += days_in_city
                break
    
    # Sort the itinerary by day_range
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))
    
    # Output the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = create_itinerary()
print(json.dumps(itinerary_json, indent=4))