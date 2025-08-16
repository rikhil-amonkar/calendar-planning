import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Oslo": {"days": 2, "must_visit": [24, 25]},
        "Helsinki": {"days": 2},
        "Edinburgh": {"days": 3},
        "Riga": {"days": 2},
        "Tallinn": {"days": 5, "must_visit": [4, 5, 6, 7, 8]},
        "Budapest": {"days": 5},
        "Vilnius": {"days": 5},
        "Porto": {"days": 5},
        "Geneva": {"days": 4}
    }

    # Define the direct flight connections
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

    # Helper function to check if a transition is possible
    def can_transition(city1, city2):
        return (city1, city2) in flights or (city2, city1) in flights

    # Helper function to check if a city can be visited on a given day
    def can_visit_city(city, day):
        if city in constraints:
            if "must_visit" in constraints[city]:
                return day in constraints[city]["must_visit"]
        return True

    # Function to add a city to the itinerary
    def add_to_itinerary(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days

    # Start with Porto as the first city
    add_to_itinerary("Porto", constraints["Porto"]["days"])

    # Visit Tallinn next to attend the wedding
    add_to_itinerary("Tallinn", constraints["Tallinn"]["days"])

    # Transition to Vilnius
    add_to_itinerary("Vilnius", constraints["Vilnius"]["days"])

    # Transition to Helsinki
    add_to_itinerary("Helsinki", constraints["Helsinki"]["days"])

    # Transition to Riga
    add_to_itinerary("Riga", constraints["Riga"]["days"])

    # Transition to Edinburgh
    add_to_itinerary("Edinburgh", constraints["Edinburgh"]["days"])

    # Transition to Budapest
    add_to_itinerary("Budapest", constraints["Budapest"]["days"])

    # Transition to Geneva
    add_to_itinerary("Geneva", constraints["Geneva"]["days"])

    # Finally, visit Oslo to meet the friend
    add_to_itinerary("Oslo", constraints["Oslo"]["days"])

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))