import json

def calculate_itinerary():
    # Define the constraints
    total_days = 15
    stuttgart_stay = 5
    stuttgart_workshop_days = range(10, 15)  # Day 11 to Day 15 (0-indexed)
    manchester_stay = 7
    manchester_wedding_days = range(0, 7)  # Day 1 to Day 7 (0-indexed)
    madrid_stay = 4
    vienna_stay = 2
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Manchester for the wedding
    itinerary.append({"day_range": f"Day 1-{manchester_stay}", "place": "Manchester"})
    current_day = manchester_stay
    
    # Move to Vienna next
    itinerary.append({"day_range": f"Day {current_day+1}-{current_day+1}", "place": "Vienna"})
    current_day += 1
    
    # Stay in Vienna for 1 more day
    itinerary.append({"day_range": f"Day {current_day+1}-{current_day+vienna_stay}", "place": "Vienna"})
    current_day += vienna_stay
    
    # Move to Madrid next
    itinerary.append({"day_range": f"Day {current_day+1}-{current_day+1}", "place": "Madrid"})
    current_day += 1
    
    # Stay in Madrid for the remaining days
    itinerary.append({"day_range": f"Day {current_day+1}-{current_day+madrid_stay}", "place": "Madrid"})
    current_day += madrid_stay
    
    # Move to Stuttgart for the workshop
    itinerary.append({"day_range": f"Day {current_day+1}-{current_day+1}", "place": "Stuttgart"})
    current_day += 1
    
    # Stay in Stuttgart for the remaining days including the workshop
    itinerary.append({"day_range": f"Day {current_day+1}-Day 15", "place": "Stuttgart"})
    
    return itinerary

# Calculate and print the itinerary in JSON format
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))