import json

def calculate_itinerary():
    # Input constraints
    total_days = 18
    split_days = 6
    santorini_days = 7
    london_days = 7
    conference_days = [12, 18]
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Split for 6 days
    itinerary.append({"day_range": f"Day 1-{split_days}", "place": "Split"})
    
    # Move to London on Day 6 and stay for 3 more days (total 6+3=9 days including transition)
    london_start_day = split_days
    london_end_day = london_start_day + london_days - 1
    itinerary.append({"day_range": f"Day {london_start_day}-{london_end_day}", "place": "London"})
    
    # Move to Santorini on Day 12 and stay for 7 days including conference days
    santorini_start_day = conference_days[0]
    santorini_end_day = santorini_start_day + santorini_days - 1
    itinerary.append({"day_range": f"Day {santorini_start_day}-{santorini_end_day}", "place": "Santorini"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())