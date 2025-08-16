import json

def calculate_itinerary():
    # Input constraints
    total_days = 20
    valencia_days = 6
    athens_days = 6
    naples_days = 5
    zurich_days = 6
    
    athens_visit_start = 1
    athens_visit_end = 6
    
    naples_wedding_start = 16
    naples_wedding_end = 20
    
    # Initialize itinerary
    itinerary = []
    
    # Day 1 to 6: Athens (visiting relatives)
    itinerary.append({"day_range": f"Day 1-{athens_visit_end}", "place": "Athens"})
    current_day = athens_visit_end + 1
    
    # Day 7 to 8: Travel to Valencia (overlapping day 8)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+1}", "place": "Valencia"})
    current_day += 2
    
    # Day 8 to 13: Valencia (5 more days)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+valencia_days-6}", "place": "Valencia"})
    current_day += valencia_days - 5
    
    # Day 14 to 15: Travel to Zurich (overlapping day 15)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+1}", "place": "Zurich"})
    current_day += 2
    
    # Day 15 to 20: Zurich (1 more day) and Naples (wedding)
    itinerary.append({"day_range": f"Day {current_day}-{naples_wedding_start-1}", "place": "Zurich"})
    itinerary.append({"day_range": f"Day {naples_wedding_start}-{naples_wedding_end}", "place": "Naples"})
    
    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))