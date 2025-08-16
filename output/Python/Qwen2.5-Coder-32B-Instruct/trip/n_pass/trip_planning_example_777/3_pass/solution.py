import json

def calculate_itinerary():
    # Define the constraints
    total_days = 15
    city_stays = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5
    }
    events = {
        "Helsinki": (3, 5),
        "Vienna": (2, 3),
        "Tallinn": (7, 11)
    }
    direct_flights = [
        ("Helsinki", "Riga"), ("Riga", "Tallinn"), ("Vienna", "Helsinki"),
        ("Riga", "Dublin"), ("Vienna", "Riga"), ("Reykjavik", "Vienna"),
        ("Helsinki", "Dublin"), ("Tallinn", "Dublin"), ("Reykjavik", "Helsinki"),
        ("Reykjavik", "Dublin"), ("Helsinki", "Tallinn"), ("Vienna", "Dublin")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    def can_travel(from_city, to_city):
        return (from_city, to_city) in direct_flights or (to_city, from_city) in direct_flights

    def add_to_itinerary(city, days):
        nonlocal current_day
        itinerary.append({"day_range": (current_day, current_day + days - 1), "place": city})
        current_day += days

    # Start in Dublin for 5 days
    add_to_itinerary("Dublin", 5)

    # Go to Vienna for 2 days (annual show on day 2-3)
    if can_travel("Dublin", "Vienna"):
        add_to_itinerary("Vienna", 2)

    # Go to Helsinki for 3 days (meet friends on day 3-5)
    if can_travel("Vienna", "Helsinki"):
        add_to_itinerary("Helsinki", 3)

    # Go to Riga for 3 days
    if can_travel("Helsinki", "Riga"):
        add_to_itinerary("Riga", 3)

    # Go to Tallinn for 5 days (wedding on day 7-11)
    if can_travel("Riga", "Tallinn"):
        add_to_itinerary("Tallinn", 5)

    # Go to Reykjavik for 2 days
    if can_travel("Tallinn", "Reykjavik"):
        add_to_itinerary("Reykjavik", 2)

    # Adjust the itinerary to fit all constraints
    adjusted_itinerary = []
    current_day = 1

    for entry in itinerary:
        start_day, end_day = entry["day_range"]
        days = end_day - start_day + 1
        place = entry["place"]

        if place == "Helsinki":
            start_day = max(current_day, events["Helsinki"][0])
            days = min(events["Helsinki"][1] - start_day + 1, days)
            adjusted_itinerary.append({"day_range": f"Day {start_day}-{start_day + days - 1}", "place": place})
            current_day = start_day + days
        elif place == "Vienna":
            start_day = max(current_day, events["Vienna"][0])
            days = min(events["Vienna"][1] - start_day + 1, days)
            adjusted_itinerary.append({"day_range": f"Day {start_day}-{start_day + days - 1}", "place": place})
            current_day = start_day + days
        elif place == "Tallinn":
            start_day = max(current_day, events["Tallinn"][0])
            days = min(events["Tallinn"][1] - start_day + 1, days)
            adjusted_itinerary.append({"day_range": f"Day {start_day}-{start_day + days - 1}", "place": place})
            current_day = start_day + days
        else:
            adjusted_itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": place})
            current_day += days

    return {"itinerary": adjusted_itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))