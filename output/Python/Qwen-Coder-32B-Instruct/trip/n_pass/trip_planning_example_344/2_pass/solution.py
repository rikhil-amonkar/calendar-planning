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
    itinerary.append({"day_range": f"Day {athens_visit_start}-{athens_visit_end}", "place": "Athens"})
    current_day = athens_visit_end + 1
    
    # Day 7 to 12: Travel to Valencia (overlapping day 12)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+valencia_days-1}", "place": "Valencia"})
    current_day += valencia_days
    
    # Day 13 to 14: Travel to Zurich (overlapping day 14)
    itinerary.append({"day_range": f"Day {current_day}-{current_day+1}", "place": "Zurich"})
    current_day += 2
    
    # Day 15 to 20: Zurich (remaining days) and Naples (wedding)
    remaining_zurich_days = zurich_days - (current_day - 14)
    if remaining_zurich_days > 0:
        itinerary.append({"day_range": f"Day {current_day}-{current_day+remaining_zurich_days-1}", "place": "Zurich"})
        current_day += remaining_zurich_days
    
    # Day 16 to 20: Naples (wedding)
    itinerary.append({"day_range": f"Day {naples_wedding_start}-{naples_wedding_end}", "place": "Naples"})
    
    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))