import json

def compute_itinerary():
    # Input parameters:
    total_days = 16

    # Planned durations (including the overlapping flight days)
    # When going from one city to the next, the flight day is shared.
    durations = {
        "Prague": 4,
        "Reykjavik": 4,
        "Munich": 4,
        "Porto": 5,
        "Amsterdam": 2,
        "Santorini": 2,
    }
    
    # Special events constraints (for reference/checks)
    wedding_window = (4, 7)        # In Reykjavik between day 4 and day 7 (inclusive)
    friend_meet_window = (7, 10)   # In Munich between day 7 and day 10 (inclusive)
    conference_days = (14, 15)     # In Amsterdam during day 14 and day 15
    
    # Direct flights available (bidirectional)
    # Represented as a set of frozensets for quick membership check.
    direct_flights = {
        frozenset(["Porto", "Amsterdam"]),
        frozenset(["Munich", "Amsterdam"]),
        frozenset(["Reykjavik", "Amsterdam"]),
        frozenset(["Munich", "Porto"]),
        frozenset(["Prague", "Reykjavik"]),
        frozenset(["Reykjavik", "Munich"]),
        frozenset(["Amsterdam", "Santorini"]),
        frozenset(["Prague", "Amsterdam"]),
        frozenset(["Prague", "Munich"]),
    }
    
    # We must visit 6 cities with durations adding to 21.
    # Overlap via 5 flights yields total days = 21 - 5 = 16.
    # We choose an ordering that respects both the direct flights and the time-event constraints:
    # Chosen order: Prague -> Reykjavik -> Munich -> Porto -> Amsterdam -> Santorini
    ordering = ["Prague", "Reykjavik", "Munich", "Porto", "Amsterdam", "Santorini"]
    
    # Verify that each leg is available as a direct flight.
    for i in range(len(ordering) - 1):
        leg = frozenset([ordering[i], ordering[i+1]])
        if leg not in direct_flights:
            raise ValueError(f"Direct flight between {ordering[i]} and {ordering[i+1]} is not available.")
    
    # Now compute the day ranges. 
    # When flying from A to B on day X, day X counts toward both A and B.
    itinerary = []
    current_day = 1
    for idx, city in enumerate(ordering):
        # The city duration includes the first day as flight-overlap from previous leg (if not the very first city)
        duration = durations[city]
        # Compute end day (both inclusive)
        # For the first city, current_day is 1; for subsequent cities, the first day is an overlap.
        end_day = current_day + duration - 1
        # Save the itinerary segment
        itinerary.append({
            "day_range": f"{current_day}-{end_day}",
            "place": city
        })
        # For all but the last city, the flight day is the end_day,
        # which counts as the start day for the next city.
        if idx < len(ordering) - 1:
            current_day = end_day  # overlap day
        
    # Check if total trip days equals total_days as expected
    last_range = itinerary[-1]["day_range"]
    trip_end_day = int(last_range.split('-')[1])
    if trip_end_day != total_days:
        raise ValueError(f"Computed trip length ({trip_end_day} days) does not equal expected total days ({total_days} days).")
    
    # Optionally, verify that special event constraints are met:
    # Wedding in Reykjavik (itinerary index 1): its day range must intersect wedding_window.
    reykjavik_range = itinerary[1]["day_range"]
    reykjavik_start, reykjavik_end = map(int, reykjavik_range.split('-'))
    if not (wedding_window[0] >= reykjavik_start and wedding_window[1] <= reykjavik_end):
        # Alternatively check if the wedding_window is contained in the stay period.
        if not (reykjavik_start <= wedding_window[0] <= reykjavik_end) or not (reykjavik_start <= wedding_window[1] <= reykjavik_end):
            raise ValueError("Wedding constraint in Reykjavik is not satisfied.")
    
    # Friend meeting in Munich (itinerary index 2): must occur between day 7 and 10.
    munich_range = itinerary[2]["day_range"]
    munich_start, munich_end = map(int, munich_range.split('-'))
    if not (munich_start <= friend_meet_window[0] <= munich_end) or not (munich_start <= friend_meet_window[1] <= munich_end):
        raise ValueError("Friend meeting constraint in Munich is not satisfied.")
    
    # Conference in Amsterdam (itinerary index 4): day14-15 must be within the Amsterdam stay.
    amsterdam_range = itinerary[4]["day_range"]
    amsterdam_start, amsterdam_end = map(int, amsterdam_range.split('-'))
    if not (amsterdam_start <= conference_days[0] <= amsterdam_end) or not (amsterdam_start <= conference_days[1] <= amsterdam_end):
        raise ValueError("Conference constraint in Amsterdam is not satisfied.")
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    plan = compute_itinerary()
    print(json.dumps(plan))