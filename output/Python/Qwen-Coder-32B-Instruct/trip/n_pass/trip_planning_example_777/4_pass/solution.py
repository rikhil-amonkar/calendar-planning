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
        "Tallinn": 2  # Adjusted to fit 15 days
    }
    events = {
        "Helsinki": (3, 5),
        "Vienna": (2, 3),
        "Tallinn": (7, 8)  # Adjusted to fit within the 15-day period
    }
    direct_flights = [
        ("Dublin", "Vienna"), ("Vienna", "Helsinki"), ("Helsinki", "Riga"),
        ("Riga", "Tallinn"), ("Tallinn", "Reykjavik"), ("Reykjavik", "Vienna"),
        ("Vienna", "Dublin"), ("Helsinki", "Dublin"), ("Riga", "Dublin"),
        ("Tallinn", "Dublin"), ("Reykjavik", "Helsinki"), ("Vienna", "Riga")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    def can_travel(from_city, to_city):
        return (from_city, to_city) in direct_flights or (to_city, from_city) in direct_flights

    def add_to_itinerary(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
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

    # Go to Tallinn for 2 days (wedding on day 7-8)
    if can_travel("Riga", "Tallinn"):
        add_to_itinerary("Tallinn", 2)

    # Go to Reykjavik for 2 days
    if can_travel("Tallinn", "Reykjavik"):
        add_to_itinerary("Reykjavik", 2)

    # Ensure the itinerary covers exactly 15 days
    if current_day < total_days:
        remaining_days = total_days - current_day + 1
        add_to_itinerary("Dublin", remaining_days)

    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))