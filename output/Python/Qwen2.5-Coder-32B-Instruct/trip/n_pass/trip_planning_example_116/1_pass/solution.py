import json

def calculate_itinerary():
    # Input variables
    total_days = 18
    split_days = 6
    santorini_days = 7
    london_days = 7
    conference_days = [12, 18]
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Split for 6 days
    itinerary.append({"day_range": f"Day 1-{split_days}", "place": "Split"})
    
    # Move to London on day 6 and stay until day 11 (6 more days)
    london_start_day = split_days
    london_end_day = london_start_day + london_days - 1
    itinerary.append({"day_range": f"Day {london_start_day}-{london_end_day}", "place": "London"})
    
    # Move to Santorini on day 11 and stay until day 18 (8 days total, including conference days)
    santorini_start_day = london_end_day
    santorini_end_day = total_days
    itinerary.append({"day_range": f"Day {santorini_start_day}-{santorini_end_day}", "place": "Santorini"})
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary()))