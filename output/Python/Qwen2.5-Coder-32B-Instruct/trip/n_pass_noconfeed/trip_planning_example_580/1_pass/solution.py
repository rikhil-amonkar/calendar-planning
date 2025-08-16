import json

def calculate_itinerary():
    # Input constraints
    total_days = 23
    days_in_paris = 6
    days_in_oslo = 5
    days_in_porto = 7
    days_in_geneva = 7
    days_in_reykjavik = 2
    geneva_conference_days = [1, 7]
    oslo_relative_visit_days = range(19, 24)

    # Initialize variables
    itinerary = []
    current_day = 1

    # Add Geneva for conference on Day 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Geneva"})
    current_day += 1

    # Add remaining days in Geneva until Day 7
    while current_day < 7:
        itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Geneva"})
        current_day += 1

    # Add Geneva for conference on Day 7
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Geneva"})
    current_day += 1

    # Add remaining days in Geneva after Day 7
    while current_day < 8 + days_in_geneva - 2:
        itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Geneva"})
        current_day += 1

    # Transition to Paris (Day 8-13)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_paris - 1}", "place": "Paris"})
    current_day += days_in_paris

    # Transition to Porto (Day 14-20)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_porto - 1}", "place": "Porto"})
    current_day += days_in_porto

    # Transition to Reykjavik (Day 21-22)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_reykjavik - 1}", "place": "Reykjavik"})
    current_day += days_in_reykjavik

    # Transition to Oslo (Day 23-27)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_oslo - 1}", "place": "Oslo"})
    current_day += days_in_oslo

    # Adjust for relative visit in Oslo (Day 19-23)
    itinerary[-1]["day_range"] = f"Day 19-{oslo_relative_visit_days.stop - 1}"

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Execute the function and print the result
print(calculate_itinerary())