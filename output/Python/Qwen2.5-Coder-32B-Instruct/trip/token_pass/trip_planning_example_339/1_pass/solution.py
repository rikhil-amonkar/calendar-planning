import json

def calculate_itinerary():
    # Define the constraints
    total_days = 17
    days_in_riga = 7
    days_in_budapest = 7
    days_in_paris = 4
    days_in_warsaw = 2
    
    # Define the show and wedding periods
    show_period = (1, 2)
    wedding_period = (11, 17)
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Warsaw for the show
    itinerary.append({"day_range": f"Day {show_period[0]}-{show_period[1]}", "place": "Warsaw"})
    
    # Transition to Budapest after the show
    itinerary.append({"day_range": f"Day {show_period[1]+1}-{show_period[1]+1}", "place": "Budapest"})
    
    # Stay in Budapest until Day 10 (to prepare for the wedding)
    itinerary.append({"day_range": f"Day {show_period[1]+2}-Day 10", "place": "Budapest"})
    
    # Transition to Riga for the wedding
    itinerary.append({"day_range": f"Day 10-Day 10", "place": "Riga"})
    
    # Stay in Riga for the wedding
    itinerary.append({"day_range": f"Day 11-Day 17", "place": "Riga"})
    
    # After the wedding, transition to Paris
    itinerary.append({"day_range": f"Day 17-Day 17", "place": "Paris"})
    
    # Stay in Paris for the remaining days
    itinerary.append({"day_range": f"Day 18-Day 20", "place": "Paris"})
    
    # Adjust the last entry to fit exactly 4 days in Paris
    itinerary[-1]["day_range"] = "Day 18-Day 21"
    
    # Remove the extra day from Paris and add it to Budapest
    itinerary[2]["day_range"] = "Day 3-Day 9"
    
    # Convert the itinerary to JSON format
    return json.dumps({"itinerary": itinerary}, indent=4)

# Calculate and print the itinerary
print(calculate_itinerary())