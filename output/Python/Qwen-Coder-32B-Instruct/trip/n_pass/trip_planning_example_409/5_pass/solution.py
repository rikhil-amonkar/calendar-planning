import json

def calculate_itinerary():
    # Define the constraints
    total_days = 12
    days_in_hamburg = 2
    days_in_zurich = 3
    days_in_split = 7  # Adjusted to fit the total days constraint

    # Initialize the itinerary
    itinerary = []

    # Start in Zurich for the first 3 days to attend the wedding
    itinerary.append({"day_range": f"1-3", "place": "Zurich"})

    # Attend the conference in Split on day 4
    itinerary.append({"day_range": f"4", "place": "Split"})

    # Stay in Split until day 10 (conference on day 10)
    itinerary.append({"day_range": f"5-10", "place": "Split"})

    # Move to Hamburg for 2 days
    itinerary.append({"day_range": f"11-12", "place": "Hamburg"})

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())