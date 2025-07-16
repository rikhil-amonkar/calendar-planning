import json

def calculate_itinerary():
    total_days = 18
    days_in_split = 5
    days_in_santorini = 7
    days_in_london = 6  # Reduced by 1 to account for no overlap
    conference_days = [12, 18]  # Must be in Santorini on these days

    # Initialize itinerary
    itinerary = []

    # Clear plan:
    # Split: days 1-5 (5 days)
    # London: days 6-11 (6 days)
    # Santorini: days 12-18 (7 days)
    # Total: 5 + 6 + 7 = 18 days

    split_start = 1
    split_end = split_start + days_in_split - 1
    itinerary.append({"day_range": f"Day {split_start}-{split_end}", "place": "Split"})

    london_start = split_end + 1  # day 6
    london_end = london_start + days_in_london - 1  # day 11
    itinerary.append({"day_range": f"Day {london_start}-{london_end}", "place": "London"})

    santorini_start = london_end + 1  # day 12
    santorini_end = santorini_start + days_in_santorini - 1  # day 18
    itinerary.append({"day_range": f"Day {santorini_start}-{santorini_end}", "place": "Santorini"})

    # Verify conference days are in Santorini
    for day in conference_days:
        if not (santorini_start <= day <= santorini_end):
            raise ValueError("Conference day not in Santorini")

    # Verify total days
    total_calculated = (split_end - split_start + 1) + (london_end - london_start + 1) + (santorini_end - santorini_start + 1)
    if total_calculated != total_days:
        raise ValueError(f"Total days do not match: expected {total_days}, got {total_calculated}")

    return {"itinerary": itinerary}

def main():
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()