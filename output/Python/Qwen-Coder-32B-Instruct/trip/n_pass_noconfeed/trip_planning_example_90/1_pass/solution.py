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
    
    # Stay in Naples first as per constraints
    itinerary.append({"day_range": f"Day {naples_visit_start}-{naples_visit_end}", "place": "Naples"})
    
    # Transition from Naples to Vienna on day 6
    itinerary.append({"day_range": f"Day {naples_visit_end+1}-{naples_visit_end+vienna_stay}", "place": "Vienna"})
    
    # Transition from Vienna to Vilnius after staying in Vienna for 7 days
    vilnius_start_day = naples_visit_end + vienna_stay + 1
    itinerary.append({"day_range": f"Day {vilnius_start_day}-{vilnius_start_day+vilnius_stay-1}", "place": "Vilnius"})
    
    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))