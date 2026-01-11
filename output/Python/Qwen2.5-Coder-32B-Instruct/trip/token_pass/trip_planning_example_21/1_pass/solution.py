import json

def generate_itinerary():
    # Define the constraints
    total_days = 10
    venice_stay = 6
    mykonos_stay = 2
    vienna_stay = 4
    venice_workshop_start = 5
    venice_workshop_end = 10

    # Construct the itinerary
    itinerary = []

    # Day 1-2: Mykonos
    itinerary.append({"day_range": "Day 1-2", "place": "Mykonos"})

    # Day 2: Flight from Mykonos to Vienna (arrive Day 2)
    # Day 3-4: Vienna
    itinerary.append({"day_range": "Day 2-4", "place": "Vienna"})

    # Day 4: Flight from Vienna to Venice (arrive Day 4)
    # Day 4-10: Venice
    itinerary.append({"day_range": "Day 4-10", "place": "Venice"})

    # Day 10: Flight from Venice to Vienna (arrive Day 10)
    # Day 10: Vienna (last day of the trip)
    itinerary.append({"day_range": "Day 10", "place": "Vienna"})

    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))