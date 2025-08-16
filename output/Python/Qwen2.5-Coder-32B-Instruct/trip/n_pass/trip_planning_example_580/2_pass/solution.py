import json

def calculate_itinerary():
    # Input variables
    total_days = 23
    days_in_paris = 6
    days_in_oslo = 5
    days_in_porto = 7
    days_in_geneva = 7
    days_in_reykjavik = 2
    oslo_visit_start = 19
    
    # Initialize itinerary
    itinerary = []
    current_day = 1
    
    # Add Geneva stay (first part)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_geneva - 1}", "place": "Geneva"})
    current_day += days_in_geneva
    
    # Add Paris stay
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_paris - 1}", "place": "Paris"})
    current_day += days_in_paris
    
    # Add Porto stay
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_porto - 1}", "place": "Porto"})
    current_day += days_in_porto
    
    # Add Geneva stay (second part)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_geneva - 1}", "place": "Geneva"})
    current_day += days_in_geneva
    
    # Add Reykjavik stay
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_reykjavik - 1}", "place": "Reykjavik"})
    current_day += days_in_reykjavik
    
    # Add Oslo stay for visiting relatives
    itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Oslo"})
    
    return itinerary

# Calculate and print the itinerary as JSON
itinerary_result = calculate_itinerary()
print(json.dumps({"itinerary": itinerary_result}))