import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5,
        "workshop": (16, 19),
        "show": (12, 13)
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    def add_to_itinerary(city, days):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days

    # Add Riga for 4 days
    add_to_itinerary("Riga", 4)

    # Add Istanbul for 2 days on Day 12-13 for the show
    add_to_itinerary("Istanbul", 2)

    # Add Bucharest for 4 days ensuring it fits before the workshop
    if current_day <= 14:
        add_to_itinerary("Bucharest", 14 - current_day)
    else:
        add_to_itinerary("Bucharest", 4)

    # Add Florence for 4 days
    add_to_itinerary("Florence", 4)

    # Add Vienna for 2 days ensuring it fits before the workshop
    if current_day <= 16:
        add_to_itinerary("Vienna", 16 - current_day)
    else:
        add_to_itinerary("Vienna", 2)

    # Add workshop for 4 days on Day 16-19
    add_to_itinerary("Workshop", 4)

    # Add Reykjavik for 4 days
    add_to_itinerary("Reykjavik", 4)

    # Add Stuttgart for 5 days
    add_to_itinerary("Stuttgart", 5)

    # Add Manchester for 5 days ensuring it fits within the 23 days
    if current_day <= 23:
        add_to_itinerary("Manchester", 23 - current_day + 1)
    else:
        add_to_itinerary("Manchester", 5)

    # Ensure the total duration is 23 days
    if current_day != 24:
        raise ValueError(f"Itinerary does not match the required duration of 23 days. Current day: {current_day}")

    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))