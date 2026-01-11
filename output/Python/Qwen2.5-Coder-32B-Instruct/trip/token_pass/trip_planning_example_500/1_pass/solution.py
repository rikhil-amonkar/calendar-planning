import json

def create_itinerary():
    # Define the required stay durations
    stay_durations = {
        "Hamburg": 7,
        "Munich": 6,
        "Manchester": 2,
        "Lyon": 2,
        "Split": 7
    }
    
    # Define the fixed days
    fixed_days = {
        "Manchester": (19, 20),
        "Lyon": (13, 14)
    }
    
    # Initialize the itinerary list
    itinerary = []
    
    # Start with Hamburg
    current_day = 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Hamburg'] - 1}", "place": "Hamburg"})
    current_day += stay_durations['Hamburg']
    
    # Move to Munich next
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Munich'] - 1}", "place": "Munich"})
    current_day += stay_durations['Munich']
    
    # Place Lyon between day 13 and 14
    # Adjust the previous entries if necessary
    if current_day <= 12:
        # Add days to reach day 13
        additional_days = 13 - current_day
        itinerary[-1]["day_range"] = f"Day {int(itinerary[-1]['day_range'].split('-')[0].split()[1])}-{int(itinerary[-1]['day_range'].split('-')[1]) + additional_days}"
        current_day += additional_days
    
    # Add Lyon days
    itinerary.append({"day_range": f"Day 13-14", "place": "Lyon"})
    current_day = 15
    
    # Move to Manchester before day 19
    if current_day <= 18:
        # Add days to reach day 18
        additional_days = 18 - current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + additional_days - 1}", "place": "Manchester"})
        current_day += additional_days
    
    # Add remaining days in Manchester
    itinerary.append({"day_range": f"Day 19-20", "place": "Manchester"})
    current_day = 21
    
    # Move to Split for the remaining days
    if current_day <= 20:
        # Add days to reach day 20
        additional_days = 20 - current_day + 1
        itinerary.append({"day_range": f"Day {current_day}-{current_day + additional_days - 1}", "place": "Split"})
    
    # Output the itinerary as JSON
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = create_itinerary()
print(json.dumps(itinerary_json, indent=4))