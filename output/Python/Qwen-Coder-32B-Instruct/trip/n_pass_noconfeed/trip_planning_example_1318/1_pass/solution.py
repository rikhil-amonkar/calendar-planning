import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Oslo": {"days": 2, "meet_friend": (24, 25)},
        "Helsinki": {"days": 2},
        "Edinburgh": {"days": 3},
        "Riga": {"days": 2},
        "Tallinn": {"days": 5, "wedding": (4, 8)},
        "Budapest": {"days": 5},
        "Vilnius": {"days": 5},
        "Porto": {"days": 5},
        "Geneva": {"days": 4}
    }
    
    # Define the flight connections
    flights = [
        ("Porto", "Oslo"), ("Edinburgh", "Budapest"), ("Edinburgh", "Geneva"),
        ("Riga", "Tallinn"), ("Edinburgh", "Porto"), ("Vilnius", "Helsinki"),
        ("Tallinn", "Vilnius"), ("Riga", "Oslo"), ("Geneva", "Oslo"),
        ("Edinburgh", "Oslo"), ("Edinburgh", "Helsinki"), ("Vilnius", "Oslo"),
        ("Riga", "Helsinki"), ("Budapest", "Geneva"), ("Helsinki", "Budapest"),
        ("Helsinki", "Oslo"), ("Edinburgh", "Riga"), ("Tallinn", "Helsinki"),
        ("Geneva", "Porto"), ("Budapest", "Oslo"), ("Helsinki", "Geneva"),
        ("Riga", "Vilnius"), ("Tallinn", "Oslo")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to add a stay to the itinerary
    def add_stay(city, start_day, duration):
        end_day = start_day + duration - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        return end_day + 1
    
    # Start from Porto as it has a direct flight to Oslo where we need to meet a friend
    current_day = add_stay("Porto", current_day, constraints["Porto"]["days"])
    
    # Visit Helsinki next as it connects to many other cities
    current_day = add_stay("Helsinki", current_day, constraints["Helsinki"]["days"])
    
    # Visit Vilnius from Helsinki
    current_day = add_stay("Vilnius", current_day, constraints["Vilnius"]["days"])
    
    # Visit Riga from Vilnius
    current_day = add_stay("Riga", current_day, constraints["Riga"]["days"])
    
    # Visit Tallinn from Riga, ensuring the wedding window is covered
    tallinn_start = max(current_day, constraints["Tallinn"]["wedding"][0])
    current_day = add_stay("Tallinn", tallinn_start, constraints["Tallinn"]["days"])
    
    # Visit Budapest from Tallinn
    current_day = add_stay("Budapest", current_day, constraints["Budapest"]["days"])
    
    # Visit Geneva from Budapest
    current_day = add_stay("Geneva", current_day, constraints["Geneva"]["days"])
    
    # Finally, visit Edinburgh from Geneva
    current_day = add_stay("Edinburgh", current_day, constraints["Edinburgh"]["days"])
    
    # Ensure we meet the friend in Oslo between day 24 and day 25
    oslo_start = constraints["Oslo"]["meet_friend"][0] - constraints["Oslo"]["days"] + 1
    if oslo_start < current_day:
        raise ValueError("Cannot meet friend in Oslo within the given constraints.")
    add_stay("Oslo", oslo_start, constraints["Oslo"]["days"])
    
    return {"itinerary": itinerary}

# Output the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))