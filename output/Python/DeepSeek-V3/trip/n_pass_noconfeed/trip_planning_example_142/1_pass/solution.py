import json

def calculate_itinerary():
    # Input parameters
    total_days = 7
    days_in_madrid = 4
    days_in_dublin = 3
    days_in_tallinn = 2
    tallinn_workshop_range = (6, 7)  # Workshop between day 6 and day 7

    # Direct flights
    direct_flights = {
        "Madrid": ["Dublin"],
        "Dublin": ["Madrid", "Tallinn"],
        "Tallinn": ["Dublin"]
    }

    # Initialize itinerary
    itinerary = []

    # Since Tallinn must be visited on day 6-7, we must be in Tallinn on day 6 and 7
    # Therefore, the last city before Tallinn must be Dublin (only direct flight)
    # So the sequence must include Dublin -> Tallinn on day 5-6 or day 6-7
    # But since Tallinn is only 2 days, and workshop is day 6-7, we must be in Tallinn on day 6 and 7
    # So transition must be on day 5-6

    # We have to spend 4 days in Madrid and 3 in Dublin, with 2 in Tallinn
    # Possible sequences:
    # Option 1: Madrid -> Dublin -> Tallinn
    # Option 2: Dublin -> Madrid -> Dublin -> Tallinn

    # Check Option 1: Madrid -> Dublin -> Tallinn
    # Madrid: days 1-4 (4 days)
    # Dublin: days 4-6 (3 days: day 4 is transition, day 5, day 6 is transition)
    # Tallinn: days 6-7 (2 days)
    # But Dublin would only have 2 full days (day 5 and part of day 4 and 6), which is less than 3

    # Option 2: Dublin -> Madrid -> Dublin -> Tallinn
    # Dublin: days 1-2 (2 days)
    # Madrid: days 2-5 (4 days: day 2 is transition, days 3,4,5)
    # Dublin: days 5-6 (1 day: day 5 is transition, day 6 is transition)
    # Tallinn: days 6-7 (2 days)
    # Total Dublin: 2 (days 1-2) + 1 (day 5-6) = 3 days
    # Total Madrid: 4 days
    # Total Tallinn: 2 days
    # This fits all constraints

    itinerary = [
        {"day_range": "Day 1-2", "place": "Dublin"},
        {"day_range": "Day 2-5", "place": "Madrid"},
        {"day_range": "Day 5-6", "place": "Dublin"},
        {"day_range": "Day 6-7", "place": "Tallinn"}
    ]

    # Verify the days spent in each city
    days_spent = {"Madrid": 0, "Dublin": 0, "Tallinn": 0}
    for entry in itinerary:
        day_range = entry["day_range"]
        place = entry["place"]
        start_day = int(day_range.split('-')[0].split(' ')[1])
        end_day = int(day_range.split('-')[1])
        duration = end_day - start_day + 1
        days_spent[place] += duration

    assert days_spent["Madrid"] == days_in_madrid
    assert days_spent["Dublin"] == days_in_dublin
    assert days_spent["Tallinn"] == days_in_tallinn

    # Verify Tallinn workshop constraint
    tallinn_days = []
    for entry in itinerary:
        if entry["place"] == "Tallinn":
            day_range = entry["day_range"]
            start_day = int(day_range.split('-')[0].split(' ')[1])
            end_day = int(day_range.split('-')[1])
            tallinn_days.extend(range(start_day, end_day + 1))
    assert all(day in tallinn_days for day in range(tallinn_workshop_range[0], tallinn_workshop_range[1] + 1))

    return {"itinerary": itinerary}

# Compute and output the itinerary
result = calculate_itinerary()
print(json.dumps(result, indent=2))