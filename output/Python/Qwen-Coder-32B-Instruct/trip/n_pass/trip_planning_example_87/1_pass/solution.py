import json

def calculate_itinerary():
    # Input variables
    total_days = 7
    days_in_riga = 2
    days_in_amsterdam = 2
    days_in_mykonos = 5
    
    # Direct flights available
    flights = {
        ("Riga", "Amsterdam"),
        ("Amsterdam", "Mykonos")
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Riga for the first 2 days
    itinerary.append({"day_range": f"Day 1-{days_in_riga}", "place": "Riga"})
    
    # Move to Amsterdam on day 2
    itinerary.append({"day_range": f"Day {days_in_riga}-3", "place": "Amsterdam"})
    
    # Stay in Amsterdam for 1 more day
    itinerary.append({"day_range": f"Day {days_in_riga+1}-{days_in_riga+days_in_amsterdam}", "place": "Amsterdam"})
    
    # Move to Mykonos on day 4
    itinerary.append({"day_range": f"Day {days_in_riga+days_in_amsterdam}-{total_days}", "place": "Mykonos"})
    
    return itinerary

# Calculate and print the itinerary as JSON
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))