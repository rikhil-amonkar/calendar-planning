import json

def calculate_itinerary():
    cities = {"Warsaw": 2, "Budapest": 7, "Paris": 4, "Riga": 7}
    direct_flights = {
        "Warsaw": ["Budapest", "Riga", "Paris"],
        "Budapest": ["Warsaw", "Paris"],
        "Paris": ["Budapest", "Warsaw", "Riga"],
        "Riga": ["Warsaw", "Paris"]
    }

    itinerary = []
    current_day = 1

    # Warsaw (days 1-2)
    itinerary.append({"day_range": f"Day 1-2", "place": "Warsaw"})
    current_day += 2 - 1  # Move to day 2 (flight day)

    # Check valid next city
    next_city = "Budapest"
    if next_city not in direct_flights["Warsaw"]:
        raise ValueError("Invalid flight path")

    # Budapest (days 2-8)
    start = current_day
    end = start + cities["Budapest"] - 1
    itinerary.append({"day_range": f"Day {start}-{end}", "place": "Budapest"})
    current_day = end

    # Check next flight
    next_city = "Paris"
    if next_city not in direct_flights["Budapest"]:
        raise ValueError("Invalid flight path")

    # Paris (days 8-11)
    start = current_day
    end = start + cities["Paris"] - 1
    itinerary.append({"day_range": f"Day {start}-{end}", "place": "Paris"})
    current_day = end

    # Final flight to Riga
    next_city = "Riga"
    if next_city not in direct_flights["Paris"]:
        raise ValueError("Invalid flight path")

    # Riga (days 11-17)
    start = current_day
    end = 17  # Enforce wedding constraint
    if end - start + 1 != cities["Riga"]:
        raise ValueError("Riga days mismatch")
    itinerary.append({"day_range": f"Day {start}-{end}", "place": "Riga"})

    return {"itinerary": itinerary}

print(json.dumps(calculate_itinerary()))