import json

def calculate_itinerary():
    # Input constraints
    total_days = 12
    brussels_days = 2
    split_days = 5
    barcelona_days = 7
    
    # Direct flights available
    flights = {
        ("Brussels", "Barcelona"),
        ("Barcelona", "Split")
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Brussels for the conference
    itinerary.append({"day_range": f"Day 1-{brussels_days}", "place": "Brussels"})
    
    # Move to Barcelona after Brussels
    start_day_barcelona = brussels_days
    end_day_barcelona = start_day_barcelona + barcelona_days - 1
    itinerary.append({"day_range": f"Day {start_day_barcelona}-{end_day_barcelona}", "place": "Barcelona"})
    
    # Move to Split after Barcelona
    start_day_split = end_day_barcelona
    end_day_split = start_day_split + split_days - 1
    itinerary.append({"day_range": f"Day {start_day_split}-{end_day_split}", "place": "Split"})
    
    # Output the itinerary as JSON
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))