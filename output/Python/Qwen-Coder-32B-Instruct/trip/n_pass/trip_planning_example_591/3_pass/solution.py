import json

def calculate_itinerary():
    # Define the constraints
    total_days = 17
    stay_duration = {
        "Stuttgart": 2,
        "Bucharest": 3,
        "Geneva": 4,
        "Valencia": 5,
        "Munich": 3
    }
    geneva_visit_window = (1, 4)
    munich_friends_meeting_window = (4, 10)
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

    # Place Geneva first due to the visit window constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_duration['Geneva'] - 1}", "place": "Geneva"})
    current_day += stay_duration["Geneva"]

    # Place Munich next due to the friends meeting window constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_duration['Munich'] - 1}", "place": "Munich"})
    current_day += stay_duration["Munich"]

    # Place Valencia next as it has direct flights to/from Munich and Bucharest
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_duration['Valencia'] - 1}", "place": "Valencia"})
    current_day += stay_duration["Valencia"]

    # Place Stuttgart next as it has a direct flight from Valencia
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_duration['Stuttgart'] - 1}", "place": "Stuttgart"})
    current_day += stay_duration["Stuttgart"]

    # Place Bucharest last as it has a direct flight from Valencia
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_duration['Bucharest'] - 1}", "place": "Bucharest"})
    current_day += stay_duration["Bucharest"]

    # Output the itinerary as JSON
    return {"itinerary": itinerary}

# Run the function and print the result
print(json.dumps(calculate_itinerary(), indent=4))