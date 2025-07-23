import json

def plan_trip():
    total_days = 12
    riga_days = 5
    vilnius_days = 7
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
    
    # Determine the possible order of visits based on flight connections
    # Possible sequences:
    # 1. Dublin -> Riga -> Vilnius
    # 2. Riga -> Dublin -> Riga -> Vilnius (but this would require more days in Riga)
    # Since we have only 5 days in Riga, the first sequence is feasible
    
    # Check if the sequence Dublin -> Riga -> Vilnius is possible
    if "Dublin" in flights and "Riga" in flights["Dublin"] and "Vilnius" in flights["Riga"]:
        itinerary = [
            {"day_range": f"Day 1-{dublin_days}", "place": "Dublin"},
            {"day_range": f"Day {dublin_days + 1}-{dublin_days + riga_days}", "place": "Riga"},
            {"day_range": f"Day {dublin_days + riga_days + 1}-{total_days}", "place": "Vilnius"}
        ]
    else:
        return {"error": "No valid flight sequence found for the given constraints."}
    
    return {"itinerary": itinerary}

# Execute the function and print the result as JSON
result = plan_trip()
print(json.dumps(result, indent=2))