import json

def calculate_itinerary():
    # Define the constraints
    total_days = 12
    days_in_hamburg = 2
    days_in_zurich = 3
    days_in_split = 6  # Adjusted to fit the total days constraint

    # Initialize the itinerary
    itinerary = []

    # Start in Zurich for the first 3 days to attend the wedding
    itinerary.append({"day_range": f"1-3", "place": "Zurich"})

    # Attend the conference in Split on day 4
    itinerary.append({"day_range": f"4", "place": "Split"})

    # Stay in Split until day 9 (conference on day 10)
    itinerary.append({"day_range": f"5-9", "place": "Split"})

    # Attend the conference in Split on day 10
    itinerary.append({"day_range": f"10", "place": "Split"})

    # Stay in Split for the remaining days needed
    remaining_days_in_split = days_in_split - (10 - 4 + 1) + 1
    if remaining_days_in_split > 0:
        itinerary.append({"day_range": f"11-12", "place": "Split"})

    # Move to Hamburg for 2 days
    itinerary.append({"day_range": f"13-14", "place": "Hamburg"})

    # Since we only have 12 days, we need to adjust the last entry to fit within 12 days
    # We can remove the last entry or adjust it to fit within the 12 days
    # In this case, we'll just ensure the last entry fits within 12 days
    if len(itinerary[-1]["day_range"].split("-")) == 2:
        start_day, end_day = map(int, itinerary[-1]["day_range"].split("-"))
        if end_day > total_days:
            itinerary[-1]["day_range"] = f"{start_day}-{total_days}"
    else:
        start_day = int(itinerary[-1]["day_range"])
        if start_day > total_days:
            itinerary.pop()  # Remove the last entry if it exceeds total days

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())