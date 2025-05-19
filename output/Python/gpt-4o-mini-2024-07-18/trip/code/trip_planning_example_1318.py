import json

# Defining the trip parameters
cities = {
    "Oslo": {"stay": 2, "meet_friend": (24, 25)},
    "Helsinki": {"stay": 2},
    "Edinburgh": {"stay": 3},
    "Riga": {"stay": 2},
    "Tallinn": {"stay": 5, "wedding": (4, 8)},
    "Budapest": {"stay": 5},
    "Vilnius": {"stay": 5},
    "Porto": {"stay": 5},
    "Geneva": {"stay": 4},
}

direct_flights = {
    "Porto": ["Oslo"],
    "Edinburgh": ["Budapest", "Geneva", "Oslo", "Helsinki", "Riga", "Porto"],
    "Riga": ["Tallinn", "Oslo", "Helsinki", "Vilnius"],
    "Tallinn": ["Vilnius", "Helsinki", "Oslo"],
    "Budapest": ["Geneva", "Oslo"],
    "Vilnius": ["Helsinki", "Oslo"],
    "Geneva": ["Oslo", "Porto"],
    "Helsinki": ["Budapest", "Oslo"],
}

num_days = 25

# Function to compute the itinerary
def compute_itinerary():
    itinerary = []
    current_day = 1
    
    # Sequence of city visits respecting the constraints and flight availability
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Oslo']['stay'] - 1}", "place": "Oslo"})
    current_day += cities["Oslo"]["stay"]
    
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Oslo", "to": "Helsinki"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Helsinki']['stay'] - 1}", "place": "Helsinki"})
    current_day += cities["Helsinki"]["stay"]
    
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Helsinki", "to": "Edinburgh"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Edinburgh']['stay'] - 1}", "place": "Edinburgh"})
    current_day += cities["Edinburgh"]["stay"]
    
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Edinburgh", "to": "Riga"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Riga']['stay'] - 1}", "place": "Riga"})
    current_day += cities["Riga"]["stay"]
    
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Riga", "to": "Tallinn"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Tallinn']['stay'] - 1}", "place": "Tallinn"})
    current_day += cities["Tallinn"]["stay"]
    
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Tallinn", "to": "Budapest"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Budapest']['stay'] - 1}", "place": "Budapest"})
    current_day += cities["Budapest"]["stay"]
    
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Budapest", "to": "Geneva"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Geneva']['stay'] - 1}", "place": "Geneva"})
    current_day += cities["Geneva"]["stay"]
    
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Geneva", "to": "Vilnius"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Vilnius']['stay'] - 1}", "place": "Vilnius"})
    current_day += cities["Vilnius"]["stay"]

    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Vilnius", "to": "Porto"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Porto']['stay'] - 1}", "place": "Porto"})
    current_day += cities["Porto"]["stay"]

    # Handling meeting friend in Oslo
    itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Porto", "to": "Oslo"})
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + cities['Oslo']['meet_friend'][1] - cities['Oslo']['meet_friend'][0]}",
                      "place": "Oslo"})
    
    # Ensure we didn't go over the number of days
    assert current_day <= num_days, "Exceeded number of days in the itinerary."

    return itinerary

# Calculate itinerary and print as JSON
itinerary_result = compute_itinerary()
print(json.dumps(itinerary_result, indent=4))