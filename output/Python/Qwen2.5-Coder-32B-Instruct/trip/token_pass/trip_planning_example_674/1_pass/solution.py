import json

def generate_itinerary():
    # Define the constraints
    days = [None] * 14
    
    # Place Helsinki (2 days with workshop on Day 1 or 2)
    days[0] = "Helsinki"
    days[1] = "Helsinki"
    
    # Place Warsaw (3 days visiting relatives on Day 9, 10, 11)
    days[8] = "Warsaw"
    days[9] = "Warsaw"
    days[10] = "Warsaw"
    
    # Place Reykjavik (2 days meeting a friend on Day 8 or 9)
    days[7] = "Reykjavik"
    days[8] = "Reykjavik"  # Overlap with Warsaw, but this is fine as per constraints
    
    # Remaining days to fill: 4 for Madrid, 4 for Split, 4 for Budapest
    # Use available flights to place these cities
    # We need to ensure we respect the flight constraints
    
    # Possible sequence: Helsinki -> Reykjavik -> Warsaw -> Madrid -> Split -> Budapest
    # Assign Madrid (4 days)
    days[2] = "Madrid"
    days[3] = "Madrid"
    days[4] = "Madrid"
    days[5] = "Madrid"
    
    # Assign Split (4 days)
    days[6] = "Split"
    days[11] = "Split"
    days[12] = "Split"
    days[13] = "Split"
    
    # Assign Budapest (4 days)
    days[11] = "Budapest"
    days[12] = "Budapest"
    days[13] = "Budapest"
    days[14] = "Budapest"
    
    # Adjust Budapest to fit without conflict
    days[5] = "Budapest"
    days[6] = "Budapest"
    days[11] = "Split"
    days[12] = "Split"
    days[13] = "Split"
    
    # Final check
    assert all(day is not None for day in days), "Not all days are assigned a city."
    
    # Create the itinerary in the required format
    itinerary = []
    start_day = 1
    current_city = days[0]
    for i in range(1, len(days)):
        if days[i] != current_city:
            itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
            start_day = i + 1
            current_city = days[i]
    itinerary.append({"day_range": f"Day {start_day}-14", "place": current_city})
    
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))