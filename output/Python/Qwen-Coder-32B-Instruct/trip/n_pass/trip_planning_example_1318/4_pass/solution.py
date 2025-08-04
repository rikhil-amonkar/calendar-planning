import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Oslo": {"days": 2, "must_visit": [24, 25]},
        "Helsinki": {"days": 2},
        "Edinburgh": {"days": 3},
        "Riga": {"days": 2},
        "Tallinn": {"days": 5, "must_visit": [4, 5, 6, 7, 8]},
        "Budapest": {"days": 4},
        "Vilnius": {"days": 4},
        "Porto": {"days": 4},
        "Geneva": {"days": 2}
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Function to add a city to the itinerary
    def add_to_itinerary(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days

    # Start with Porto as the first city
    add_to_itinerary("Porto", constraints["Porto"]["days"])

    # Visit Tallinn next to attend the wedding
    add_to_itinerary("Tallinn", constraints["Tallinn"]["days"])  # Must visit on days 4-8

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