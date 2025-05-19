import json

def compute_itinerary():
    # Input parameters (in days)
    total_days = 15
    stuttgart_days_required = 6
    seville_days_required = 7
    manchester_days_required = 4

    # Allowed direct flights:
    # - Stuttgart <-> Manchester
    # - Manchester <-> Seville
    # Hence, only viable route meeting the constraints is:
    # Stuttgart -> Manchester -> Seville
    #
    # Flight rule: if flying on day X, then that day counts for both origin and destination.
    # This means that in our total counts the two flight days are double-counted,
    # so the sum of city durations (6 + 4 + 7 = 17) - 2 (flight overlaps) = 15 total days.
    
    # We choose to fly from Stuttgart to Manchester on the last day in Stuttgart.
    # And then fly from Manchester to Seville on the last day in Manchester.
    
    # Compute itinerary day ranges:
    # Stuttgart segment: start at day 1 and end at day stuttgart_days_required.
    stuttgart_start = 1
    stuttgart_end = stuttgart_start + stuttgart_days_required - 1  # 6
    
    # Manchester segment:
    # Flight from Stuttgart occurs on day stuttgart_end.
    manchester_start = stuttgart_end  # This day counts for both Stuttgart and Manchester.
    manchester_end = manchester_start + manchester_days_required - 1  # 6 + 4 - 1 = 9
    
    # Seville segment:
    # Flight from Manchester occurs on day manchester_end.
    seville_start = manchester_end  # This day counts for both Manchester and Seville.
    seville_end = seville_start + seville_days_required - 1  # 9 + 7 - 1 = 15
    
    # Ensure total days match (taking into account the double counted flight days)
    # Total itinerary days = (stuttgart_days_required + manchester_days_required + seville_days_required) - 2 = 17 - 2 = 15
    if (stuttgart_days_required + manchester_days_required + seville_days_required - 2) != total_days:
        raise ValueError("The segments do not add up to the total days.")
    
    # Friend meeting constraint: A friend meeting must occur in Stuttgart between day 1 and day 6.
    # Our Stuttgart segment is day 1 to day 6, so we can schedule the meeting on any day in that range.
    friend_meeting_day = stuttgart_start  # For example, day 1 (or any day until day 6)
    # (This variable is computed logically, though not output, as the meeting is within the Stuttgart segment.)
    
    itinerary = [
        {"day_range": f"Day {stuttgart_start} - Day {stuttgart_end}", "place": "Stuttgart"},
        {"day_range": f"Day {manchester_start} - Day {manchester_end}", "place": "Manchester"},
        {"day_range": f"Day {seville_start} - Day {seville_end}", "place": "Seville"},
    ]
    
    return itinerary

if __name__ == "__main__":
    plan = compute_itinerary()
    print(json.dumps(plan))