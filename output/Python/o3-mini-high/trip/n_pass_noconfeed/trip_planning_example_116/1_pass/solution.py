import json

def compute_itinerary():
    # Trip constraints
    total_days = 18

    # City constraints (required days counted with flight overlap)
    days_in_split = 6
    days_in_santorini = 7
    days_in_london = 7

    # Conference days: these days must be spent in Santorini (even if as a flight day)
    conference_days = {12, 18}

    # Allowed direct flight connections (bidirectional)
    allowed_flights = {
        ("London", "Santorini"),
        ("Santorini", "London"),
        ("Split", "London"),
        ("London", "Split")
    }

    # Our itinerary will include 3 cities: Split, London, and Santorini.
    # Given the flight restrictions, and the need to have Santorini on conference days (day 12 and 18),
    # the only valid order is: Split -> London -> Santorini.
    itinerary_order = ["Split", "London", "Santorini"]

    # Check if the chosen transitions are allowed:
    transitions = [(itinerary_order[i], itinerary_order[i+1]) for i in range(len(itinerary_order)-1)]
    for frm, to in transitions:
        if (frm, to) not in allowed_flights:
            raise ValueError(f"Direct flight from {frm} to {to} is not available.")

    # Compute itinerary segments.
    # When flying on the transition day X, the traveler is considered to be in both departure and arrival cities on that day.
    # We choose flight days as the last day of the current segment.
    # So we start in Split from day 1 to day_split_end.
    start_day = 1
    split_start = start_day
    split_end = split_start + days_in_split - 1  # flight to next city on the last day of the Split segment

    # Now for London: the flight day from Split counts for London as well.
    london_start = split_end  # same as flight day from Split to London
    london_end = london_start + days_in_london - 1  # flight to next city on the last day of London segment

    # Santorini: similarly, flight day from London counts for Santorini.
    santorini_start = london_end  # same as flight day from London to Santorini
    santorini_end = santorini_start + days_in_santorini - 1

    # Validate that our overall unique days count meets the total_days constraint.
    # Unique days = days in Split + days in London + days in Santorini - (number of flight overlap days)
    # There are 2 flight transitions, so total unique days = 6 + 7 + 7 - 2 = 18.
    unique_days = days_in_split + days_in_london + days_in_santorini - len(transitions)
    if unique_days != total_days:
        raise ValueError("The planned itinerary does not sum up to the total number of days available.")

    # Ensure the conference days happen in Santorini.
    # Santorini segment covers days [santorini_start, santorini_end].
    santorini_days = set(range(santorini_start, santorini_end + 1))
    if not conference_days.issubset(santorini_days):
        raise ValueError("Conference days do not fall within the Santorini segment of the itinerary.")

    # Build itinerary segments as a list of dictionaries.
    itinerary = [
        {"day_range": f"Day {split_start}-{split_end}", "place": "Split"},
        {"day_range": f"Day {london_start}-{london_end}", "place": "London"},
        {"day_range": f"Day {santorini_start}-{santorini_end}", "place": "Santorini"}
    ]

    # Return the result as a JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    return result

if __name__ == "__main__":
    itinerary_plan = compute_itinerary()
    print(json.dumps(itinerary_plan))