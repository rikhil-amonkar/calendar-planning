import json

def calculate_itinerary():
    # Define the constraints
    total_days = 12
    days_in_hamburg = 2
    days_in_zurich = 3
    days_in_helsinki = 2
    days_in_bucharest = 2
    days_in_split = 7
    conference_days_in_split = [4, 10]
    wedding_days_in_zurich = [1, 2, 3]

    # Define the direct flight connections
    connections = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Helsinki', 'Zurich', 'Bucharest', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }

    # Initialize the itinerary
    itinerary = []

    # Start in Split for the first 3 days to attend the wedding
    itinerary.append({"day_range": f"Day 1-3", "place": "Zurich"})

    # Stay in Zurich for the wedding days
    current_day = 4

    # Attend the conference in Split on day 4
    itinerary.append({"day_range": f"Day 4", "place": "Split"})
    current_day += 1

    # Stay in Split until day 9 (conference on day 10)
    itinerary.append({"day_range": f"Day 5-9", "place": "Split"})
    current_day = 10

    # Attend the conference in Split on day 10
    itinerary.append({"day_range": f"Day 10", "place": "Split"})
    current_day += 1

    # Stay in Split for the remaining days needed
    remaining_days_in_split = days_in_split - (current_day - 4) + 1
    if remaining_days_in_split > 0:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + remaining_days_in_split - 1}", "place": "Split"})
        current_day += remaining_days_in_split

    # Move to Hamburg for 2 days
    if current_day <= total_days:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_hamburg - 1}", "place": "Hamburg"})
        current_day += days_in_hamburg

    # Move to Helsinki for 2 days
    if current_day <= total_days:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_helsinki - 1}", "place": "Helsinki"})
        current_day += days_in_helsinki

    # Move to Bucharest for 2 days
    if current_day <= total_days:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_bucharest - 1}", "place": "Bucharest"})
        current_day += days_in_bucharest

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())