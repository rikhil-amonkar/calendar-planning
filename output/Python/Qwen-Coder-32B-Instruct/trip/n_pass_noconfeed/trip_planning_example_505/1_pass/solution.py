import json

def calculate_itinerary():
    # Define the constraints
    total_days = 8
    stays = {
        "Prague": 4,
        "Stuttgart": 2,
        "Split": 2,
        "Krakow": 2,
        "Florence": 2
    }
    wedding_days = (2, 3)
    meet_friends_days = (3, 4)
    direct_flights = {
        ("Stuttgart", "Split"),
        ("Prague", "Florence"),
        ("Krakow", "Stuttgart"),
        ("Krakow", "Split"),
        ("Split", "Prague"),
        ("Krakow", "Prague")
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None

    # Function to add a stay to the itinerary
    def add_stay(city, start_day, duration):
        nonlocal current_day
        end_day = start_day + duration - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1

    # Start in Prague for 4 days
    add_stay("Prague", current_day, stays["Prague"])

    # Move to Split for 2 days (meets friends on day 3-4)
    if (current_day, current_day + 1) == meet_friends_days:
        add_stay("Split", current_day, stays["Split"])
    else:
        raise ValueError("Cannot meet friends on the specified days with current itinerary.")

    # Move to Krakow for 2 days
    if ("Split", "Krakow") in direct_flights:
        add_stay("Krakow", current_day, stays["Krakow"])
    else:
        raise ValueError("No direct flight from Split to Krakow.")

    # Move to Stuttgart for 2 days (wedding on day 2-3)
    if ("Krakow", "Stuttgart") in direct_flights and (current_day, current_day + 1) == wedding_days:
        add_stay("Stuttgart", current_day, stays["Stuttgart"])
    else:
        raise ValueError("Cannot attend wedding on the specified days with current itinerary.")

    # Move back to Prague for the remaining days
    if ("Stuttgart", "Prague") in direct_flights:
        add_stay("Prague", current_day, total_days - current_day + 1)
    else:
        raise ValueError("No direct flight from Stuttgart to Prague.")

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())