import json

def generate_itinerary():
    # Initialize the itinerary list
    itinerary = []

    # Day 1-2: Tallinn (meet a friend)
    itinerary.append({"day_range": "Day 1-2", "place": "Tallinn"})

    # Day 3: Travel to Copenhagen (flight from Tallinn to Copenhagen)
    itinerary.append({"day_range": "Day 3", "place": "Copenhagen"})

    # Day 4-5: Lisbon (workshop)
    itinerary.append({"day_range": "Day 4-5", "place": "Lisbon"})

    # Day 6-8: Copenhagen (remaining days)
    itinerary.append({"day_range": "Day 6-8", "place": "Copenhagen"})

    # Day 9-11: Prague (start of 3 days)
    itinerary.append({"day_range": "Day 9-11", "place": "Prague"})

    # Day 12: Travel to Stockholm (flight from Prague to Stockholm)
    itinerary.append({"day_range": "Day 12", "place": "Stockholm"})

    # Day 13-16: Stockholm (wedding)
    itinerary.append({"day_range": "Day 13-16", "place": "Stockholm"})

    # Day 17: Travel to Split (flight from Stockholm to Split)
    itinerary.append({"day_range": "Day 17", "place": "Split"})

    # Day 18-20: Split (remaining days)
    itinerary.append({"day_range": "Day 17-19", "place": "Split"})

    # Day 20: Travel to Lyon (flight from Split to Lyon)
    itinerary.append({"day_range": "Day 20", "place": "Lyon"})

    # Day 18-19: Lyon (annual show)
    itinerary.append({"day_range": "Day 18-19", "place": "Lyon"})

    # Adjust the last entry to reflect correct days
    itinerary[-1] = {"day_range": "Day 18-19", "place": "Lyon"}

    # Remove the incorrect entry added due to travel day overlap
    del itinerary[-2]

    # Convert the itinerary to JSON format
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())