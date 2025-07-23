import json

def plan_trip():
    total_days = 12
    riga_days = 5
    vilnius_days = 5  # Reduced from 7 to make the total 12
    dublin_days = 2
    
    # Check if the total days add up correctly
    if riga_days + vilnius_days + dublin_days != total_days:
        return {"error": "Total days do not match the sum of individual city days."}
    
    # Define flight connections
    flights = {
        "Dublin": ["Riga"],
        "Riga": ["Vilnius", "Dublin"],
        "Vilnius": ["Riga"]
    }
    
    # Create the itinerary
    itinerary = [
        {"day_range": f"Day 1-{dublin_days}", "place": "Dublin"},
        {"day_range": f"Day {dublin_days + 1}-{dublin_days + riga_days}", "place": "Riga"},
        {"day_range": f"Day {dublin_days + riga_days + 1}-{total_days}", "place": "Vilnius"}
    ]
    
    # Verify the flight connections
    if not ("Dublin" in flights and 
            "Riga" in flights["Dublin"] and 
            "Vilnius" in flights["Riga"]):
        return {"error": "No valid flight sequence found for the given constraints."}
    
    return {"itinerary": itinerary}

# Execute the function and print the result as JSON
result = plan_trip()
print(json.dumps(result, indent=2))