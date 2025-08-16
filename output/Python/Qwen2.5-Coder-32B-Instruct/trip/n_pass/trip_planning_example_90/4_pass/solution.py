import json

def calculate_itinerary():
    # Input variables
    total_days = 17
    vilnius_stay = 5
    naples_stay = 5
    vienna_stay = 7
    
    # Initialize itinerary list
    itinerary = []
    
    # Visit Naples from Day 1 to Day 5
    naples_visit_start = 1
    naples_visit_end = naples_visit_start + naples_stay - 1
    itinerary.append({"day_range": f"Day {naples_visit_start}-{naples_visit_end}", "place": "Naples"})
    
    # Visit Vienna from Day 6 to Day 12
    vienna_start_day = naples_visit_end + 1
    vienna_end_day = vienna_start_day + vienna_stay - 1
    itinerary.append({"day_range": f"Day {vienna_start_day}-{vienna_end_day}", "place": "Vienna"})
    
    # Visit Vilnius from Day 13 to Day 17
    vilnius_start_day = vienna_end_day + 1
    vilnius_end_day = vilnius_start_day + vilnius_stay - 1
    itinerary.append({"day_range": f"Day {vilnius_start_day}-{vilnius_end_day}", "place": "Vilnius"})
    
    # Ensure the total days are covered
    if vilnius_end_day != total_days:
        raise ValueError("The itinerary does not cover the entire duration of the trip.")
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))