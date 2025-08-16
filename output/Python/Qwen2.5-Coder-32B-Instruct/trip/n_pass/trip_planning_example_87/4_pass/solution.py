import json

def calculate_itinerary():
    # Define the total number of days and days spent in each city
    total_days = 7
    days_in_riga = 2
    days_in_amsterdam = 2
    days_in_mykonos = total_days - (days_in_riga + days_in_amsterdam)  # Calculate remaining days for Mykonos
    
    # Initialize the itinerary list
    itinerary = []
    
    # Add the stay in Riga
    itinerary.append({
        "day_range": f"Day 1-{days_in_riga}",
        "place": "Riga"
    })
    
    # Calculate start and end days for Amsterdam
    start_day_amsterdam = days_in_riga + 1
    end_day_amsterdam = start_day_amsterdam + days_in_amsterdam - 1
    
    # Add the stay in Amsterdam
    itinerary.append({
        "day_range": f"Day {start_day_amsterdam}-{end_day_amsterdam}",
        "place": "Amsterdam"
    })
    
    # Calculate start and end days for Mykonos
    start_day_mykonos = end_day_amsterdam + 1
    end_day_mykonos = total_days
    
    # Add the stay in Mykonos
    itinerary.append({
        "day_range": f"Day {start_day_mykonos}-{end_day_mykonos}",
        "place": "Mykonos"
    })
    
    return itinerary

# Calculate and print the itinerary as JSON
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result, indent=4))