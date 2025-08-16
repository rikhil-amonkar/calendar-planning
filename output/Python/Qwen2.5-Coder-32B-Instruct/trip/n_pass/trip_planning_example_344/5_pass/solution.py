import json

def calculate_itinerary():
    # Input constraints
    total_days = 20
    valencia_days = 6
    athens_days = 6
    naples_days = 4  # Reduced from 5 to 4
    zurich_days = 4  # Reduced from 6 to 4
    
    # Initialize itinerary
    itinerary = []
    
    # Day 1 to 6: Athens (visiting relatives)
    itinerary.append({"day_range": f"Day 1-{athens_days}", "place": "Athens"})
    current_day = athens_days + 1
    
    # Day 7 to 12: Valencia
    itinerary.append({"day_range": f"Day {current_day}-{current_day+valencia_days-1}", "place": "Valencia"})
    current_day += valencia_days
    
    # Day 13 to 16: Zurich
    itinerary.append({"day_range": f"Day {current_day}-{current_day+zurich_days-1}", "place": "Zurich"})
    current_day += zurich_days
    
    # Day 17 to 20: Naples (wedding)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+naples_days-1}", "place": "Naples"})
    
    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result, indent=4))