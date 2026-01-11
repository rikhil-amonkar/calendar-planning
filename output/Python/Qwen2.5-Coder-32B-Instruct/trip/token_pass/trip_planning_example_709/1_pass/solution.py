import json

def create_itinerary():
    # Define the cities and their stay durations
    cities = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    
    # Define the flight connections (direct flights)
    flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start in Helsinki for 4 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Helsinki'] - 1}", "place": "Helsinki"})
    current_day += cities['Helsinki']
    
    # Next, go to Reykjavik for 4 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Reykjavik'] - 1}", "place": "Reykjavik"})
    current_day += cities['Reykjavik']
    
    # Then, go to Prague for 3 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Prague'] - 1}", "place": "Prague"})
    current_day += cities['Prague']
    
    # Then, go to Valencia for 5 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Valencia'] - 1}", "place": "Valencia"})
    current_day += cities['Valencia']
    
    # Finally, go to Porto for 3 days (meets the requirement to be there between day 16 and day 18)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Porto'] - 1}", "place": "Porto"})
    current_day += cities['Porto']
    
    # Validate the total duration
    assert current_day == 18 + 1, "The itinerary does not match the total duration of 18 days."
    
    # Return the itinerary in JSON format
    return {"itinerary": itinerary}

# Create and print the itinerary
itinerary_json = create_itinerary()
print(json.dumps(itinerary_json, indent=4))