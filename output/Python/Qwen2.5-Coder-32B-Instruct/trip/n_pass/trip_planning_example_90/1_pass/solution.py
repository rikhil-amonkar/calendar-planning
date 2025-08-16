import json

def calculate_itinerary():
    # Input variables
    total_days = 17
    vilnius_stay = 7
    naples_stay = 5
    vienna_stay = 7
    naples_visit_start = 1
    naples_visit_end = 5
    
    # Initialize itinerary list
    itinerary = []
    
    # Since we need to visit Naples between day 1 and day 5, we start there
    itinerary.append({"day_range": f"Day {naples_visit_start}-{naples_visit_end}", "place": "Naples"})
    
    # After visiting relatives in Naples, we can go to Vienna
    vienna_start_day = naples_visit_end
    vienna_end_day = vienna_start_day + vienna_stay - 1
    itinerary.append({"day_range": f"Day {vienna_start_day}-{vienna_end_day}", "place": "Vienna"})
    
    # Finally, we go to Vilnius
    vilnius_start_day = vienna_end_day + 1
    vilnius_end_day = vilnius_start_day + vilnius_stay - 1
    itinerary.append({"day_range": f"Day {vilnius_start_day}-{vilnius_end_day}", "place": "Vilnius"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))