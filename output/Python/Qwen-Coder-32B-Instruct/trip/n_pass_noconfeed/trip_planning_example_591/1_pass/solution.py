import json

def calculate_itinerary():
    # Define the constraints
    total_days = 17
    stays = {
        "Stuttgart": 2,
        "Bucharest": 2,
        "Geneva": 4,
        "Valencia": 6,
        "Munich": 7
    }
    geneva_visit_window = (1, 4)
    munich_friends_window = (4, 10)
    direct_flights = {
        ("Geneva", "Munich"),
        ("Munich", "Valencia"),
        ("Bucharest", "Valencia"),
        ("Munich", "Bucharest"),
        ("Valencia", "Stuttgart"),
        ("Geneva", "Valencia")
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Place Geneva first within the visit window
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stays['Geneva'] - 1}", "place": "Geneva"})
    current_day += stays["Geneva"]

    # Place Munich next within the friends window
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stays['Munich'] - 1}", "place": "Munich"})
    current_day += stays["Munich"]

    # Place Valencia next
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stays['Valencia'] - 1}", "place": "Valencia"})
    current_day += stays["Valencia"]

    # Place Bucharest next
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stays['Bucharest'] - 1}", "place": "Bucharest"})
    current_day += stays["Bucharest"]

    # Place Stuttgart last
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stays['Stuttgart'] - 1}", "place": "Stuttgart"})
    current_day += stays["Stuttgart"]

    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output))