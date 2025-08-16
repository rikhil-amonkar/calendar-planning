import json

def calculate_itinerary():
    # Input constraints
    total_days = 15
    stuttgart_days = 6
    manchester_days = 3
    seville_days = 6
    
    # Direct flights available
    flights = {
        ('Manchester', 'Seville'): True,
        ('Stuttgart', 'Manchester'): True
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Meeting friend constraint: must be in Stuttgart between day 1 and day 6
    # Start in Stuttgart for the first 6 days
    itinerary.append({"day_range": f"Day 1-{stuttgart_days}", "place": "Stuttgart"})
    
    # After leaving Stuttgart, go to Manchester (day 7)
    current_day = stuttgart_days + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + manchester_days - 1}", "place": "Manchester"})
    current_day += manchester_days
    
    # From Manchester, go to Seville (day 10)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + seville_days - 1}", "place": "Seville"})
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary()))