import json

def plan_trip():
    # Define trip constraints
    split_days = 6
    santorini_days = 7
    london_days = 7
    conference_day1 = 12
    conference_day2 = 18

    # Calculate Santorini stay (must include both conference days)
    santorini_start = conference_day1
    santorini_end = conference_day2

    # Calculate London stay (must end on the day of flight to Santorini)
    london_end = santorini_start  # Flight to Santorini on this day
    london_start = london_end - london_days + 1  # Start day to achieve 7 days in London

    # Calculate Split stay (must end on the day of flight to London)
    split_end = london_start  # Flight to London on this day
    split_start = split_end - split_days + 1  # Start day to achieve 6 days in Split

    # Create itinerary with calculated day ranges
    itinerary = [
        {"day_range": f"Day {split_start}-{split_end}", "place": "Split"},
        {"day_range": f"Day {london_start}-{london_end}", "place": "London"},
        {"day_range": f"Day {santorini_start}-{santorini_end}", "place": "Santorini"}
    ]

    # Validation checks (can be removed in production)
    assert (split_end - split_start + 1) == split_days, "Invalid Split duration"
    assert (london_end - london_start + 1) == london_days, "Invalid London duration"
    assert (santorini_end - santorini_start + 1) == santorini_days, "Invalid Santorini duration"
    assert santorini_end == 18, "Trip doesn't end on day 18"

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, indent=2))