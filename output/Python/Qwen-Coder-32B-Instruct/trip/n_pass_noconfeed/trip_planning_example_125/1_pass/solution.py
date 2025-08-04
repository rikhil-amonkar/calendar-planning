import json

def calculate_itinerary():
    # Input variables
    total_days = 15
    stuttgart_days = 6
    seville_days = 7
    manchester_days = 4
    stuttgart_visit_day_min = 1
    stuttgart_visit_day_max = 6
    
    # Initialize itinerary list
    itinerary = []
    
    # Determine the start day for Stuttgart
    stuttgart_start_day = max(stuttgart_visit_day_min, 1)
    stuttgart_end_day = stuttgart_start_day + stuttgart_days - 1
    
    # Add Stuttgart to the itinerary
    itinerary.append({"day_range": f"Day {stuttgart_start_day}-{stuttgart_end_day}", "place": "Stuttgart"})
    
    # Determine the start day for Manchester (must be after Stuttgart ends)
    manchester_start_day = stuttgart_end_day - manchester_days + 1
    manchester_end_day = manchester_start_day + manchester_days - 1
    
    # Add Manchester to the itinerary
    itinerary.append({"day_range": f"Day {manchester_start_day}-{manchester_end_day}", "place": "Manchester"})
    
    # Determine the start day for Seville (must be after Manchester ends)
    seville_start_day = manchester_end_day - seville_days + 1
    seville_end_day = seville_start_day + seville_days - 1
    
    # Add Seville to the itinerary
    itinerary.append({"day_range": f"Day {seville_start_day}-{seville_end_day}", "place": "Seville"})
    
    # Output the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))