import json

def calculate_itinerary():
    # Input variables
    total_days = 7
    days_in_riga = 2
    days_in_amsterdam = 2
    days_in_mykonos = total_days - (days_in_riga + days_in_amsterdam)  # Calculate remaining days for Mykonos
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Riga for the first 2 days
    itinerary.append({"day_range": f"Day 1-{days_in_riga}", "place": "Riga"})
    
    # Move to Amsterdam on day 3
    start_day_amsterdam = days_in_riga + 1
    end_day_amsterdam = start_day_amsterdam + days_in_amsterdam - 1
    itinerary.append({"day_range": f"Day {start_day_amsterdam}-{end_day_amsterdam}", "place": "Amsterdam"})
    
    # Move to Mykonos on day 5
    start_day_mykonos = end_day_amsterdam + 1
    end_day_mykonos = total_days
    itinerary.append({"day_range": f"Day {start_day_mykonos}-{end_day_mykonos}", "place": "Mykonos"})
    
    return itinerary

# Calculate and print the itinerary as JSON
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result, indent=4))