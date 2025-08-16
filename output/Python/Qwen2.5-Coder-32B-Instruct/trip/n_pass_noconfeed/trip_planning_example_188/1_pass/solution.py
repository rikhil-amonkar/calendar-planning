import json

def calculate_itinerary():
    # Input variables
    total_days = 12
    brussels_days = 2
    split_days = 5
    barcelona_days = 7
    
    # Direct flights available
    flights = {
        ('Brussels', 'Barcelona'): True,
        ('Barcelona', 'Split'): True
    }
    
    # Itinerary calculation
    itinerary = []
    
    # Start in Brussels for the conference
    itinerary.append({"day_range": f"Day 1-{brussels_days}", "place": "Brussels"})
    
    # Move from Brussels to Barcelona
    current_day = brussels_days + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + barcelona_days - 1}", "place": "Barcelona"})
    
    # Move from Barcelona to Split
    current_day += barcelona_days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + split_days - 1}", "place": "Split"})
    
    return {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(calculate_itinerary(), indent=4))