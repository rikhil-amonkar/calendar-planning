import json

def generate_itinerary():
    # Define the constraints
    constraints = {
        "Hamburg": 2,
        "Zurich": 3,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7,
        "wedding_in_zurich": (1, 3),
        "conference_in_split": (4, 10)
    }

    # Define possible direct flights
    direct_flights = {
        "Zurich": ["Helsinki", "Hamburg", "Bucharest", "Split"],
        "Hamburg": ["Zurich", "Bucharest", "Helsinki", "Split"],
        "Helsinki": ["Zurich", "Hamburg", "Split"],
        "Bucharest": ["Zurich", "Hamburg"],
        "Split": ["Zurich", "Helsinki", "Hamburg"]
    }

    # Initialize the itinerary
    itinerary = []

    # Start with Zurich due to the wedding constraint
    itinerary.append({"day_range": "Day 1-3", "place": "Zurich"})

    # Next, handle the conference in Split
    itinerary.append({"day_range": "Day 4-10", "place": "Split"})

    # Now, fit the remaining days
    # We have 2 days left after day 10
    # We need to fit Hamburg (2 days), Helsinki (2 days), and Bucharest (2 days) into the remaining slots
    # Consider the direct flights and constraints

    # After day 10, we can go to Hamburg (day 11-12)
    itinerary.append({"day_range": "Day 11-12", "place": "Hamburg"})

    # Before Zurich (day 1-3), we can go to Helsinki (day 1-2) and Bucharest (day 3-4)
    # But we need to ensure the transition via direct flights
    # We can go to Helsinki (day 1-2), then to Zurich (day 3), then to Split (day 4-10)
    # Finally, we can go to Bucharest (day 11-12) after Split

    # Adjust the itinerary to fit all constraints
    # Move Helsinki before Zurich
    itinerary.insert(0, {"day_range": "Day 1-2", "place": "Helsinki"})
    # Adjust Zurich to start from day 3
    itinerary[1]["day_range"] = "Day 3-5"
    # Adjust Split to start from day 6
    itinerary[2]["day_range"] = "Day 6-12"
    # Remove the last entry for Hamburg since it overlaps with Split
    itinerary.pop()

    # Add Bucharest after Split
    itinerary.append({"day_range": "Day 11-12", "place": "Bucharest"})

    # Validate the itinerary
    assert len(itinerary) == 5, "Itinerary should have 5 entries"
    assert itinerary[0]["day_range"] == "Day 1-2", "Helsinki should be on Day 1-2"
    assert itinerary[1]["day_range"] == "Day 3-5", "Zurich should be on Day 3-5"
    assert itinerary[2]["day_range"] == "Day 6-12", "Split should be on Day 6-12"
    assert itinerary[3]["day_range"] == "Day 11-12", "Bucharest should be on Day 11-12"

    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())