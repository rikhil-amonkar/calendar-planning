import json

def calculate_itinerary(total_days=7, days_in_riga=2, days_in_amsterdam=2):
    # Initialize the itinerary list
    itinerary = []
    
    # Calculate the end day for Riga
    end_day_riga = days_in_riga
    
    # Add the stay in Riga
    itinerary.append({
        "day_range": f"Day 1-{end_day_riga}",
        "place": "Riga"
    })
    
    # Calculate start and end days for Amsterdam
    start_day_amsterdam = end_day_riga + 1
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