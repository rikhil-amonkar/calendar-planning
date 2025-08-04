import json

def calculate_itinerary():
    # Input constraints
    total_days = 15
    stuttgart_days = 6
    stuttgart_start_day = 10
    stuttgart_end_day = stuttgart_start_day + stuttgart_days - 1
    
    manchester_days = 7
    manchester_start_day = 1
    manchester_end_day = manchester_start_day + manchester_days - 1
    
    vienna_days = 2
    vienna_start_day = manchester_end_day + 1  # Ensure Vienna starts after Manchester ends
    vienna_end_day = vienna_start_day + vienna_days - 1
    
    # Initialize itinerary
    itinerary = []
    
    # Manchester stay (Day 1-7)
    itinerary.append({"day_range": f"Day {manchester_start_day}-{manchester_end_day}", "place": "Manchester"})
    
    # Vienna stay (Day 8-9)
    itinerary.append({"day_range": f"Day {vienna_start_day}-{vienna_end_day}", "place": "Vienna"})
    
    # Stuttgart stay (Day 10-15)
    itinerary.append({"day_range": f"Day {stuttgart_start_day}-{stuttgart_end_day}", "place": "Stuttgart"})
    
    return itinerary

# Calculate and output the itinerary as JSON
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))