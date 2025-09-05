import itertools
import json

# Trip constraints
total_days = 19
city_durations = {
    "Dubrovnik": 5,
    "Warsaw": 2,
    "Stuttgart": 7,
    "Bucharest": 6,
    "Copenhagen": 3
}

# Direct flight connections (bidirectional)
flight_connections = {
    frozenset(["Warsaw", "Copenhagen"]),
    frozenset(["Stuttgart", "Copenhagen"]),
    frozenset(["Warsaw", "Stuttgart"]),
    frozenset(["Bucharest", "Copenhagen"]),
    frozenset(["Bucharest", "Warsaw"]),
    frozenset(["Copenhagen", "Dubrovnik"])
}

# Special constraints:
# - Wedding in Bucharest must happen between day 1 and day 6.
# - Conference in Stuttgart must be attended on day 7 and day 13.
def satisfies_special_constraints(itinerary_segments):
    bucharest_seg = next((seg for seg in itinerary_segments if seg["place"] == "Bucharest"), None)
    stuttgart_seg = next((seg for seg in itinerary_segments if seg["place"] == "Stuttgart"), None)
    # Check Bucharest wedding: The Bucharest segment must include at least one day in [1,6].
    if bucharest_seg:
        # If the start day is after day 6, wedding constraint fails.
        if bucharest_seg["start_day"] > 6:
            return False
    else:
        return False
    # Check Stuttgart conferences: Stuttgart segment must include both day 7 and day 13.
    if stuttgart_seg:
        if stuttgart_seg["start_day"] > 7 or stuttgart_seg["end_day"] < 13:
            return False
    else:
        return False
    return True

# Check that for every consecutive pair in the order, a direct flight exists.
def valid_flight_sequence(order):
    for i in range(len(order) - 1):
        if frozenset([order[i], order[i+1]]) not in flight_connections:
            return False
    return True

# Given an order of cities, compute the itinerary segments.
# If flying from city A to city B on a transition day, that day is counted in both cities.
def compute_itinerary(order, durations):
    segments = []
    current_day = 1
    for idx, city in enumerate(order):
        if idx == 0:
            # First city: spend full duration from current_day to (current_day + duration - 1)
            start_day = current_day
            end_day = current_day + durations[city] - 1
        else:
            # For subsequent cities, the flight day is the same as the previous segment end_day.
            start_day = current_day
            end_day = start_day + durations[city] - 1
        segments.append({
            "place": city,
            "start_day": start_day,
            "end_day": end_day
        })
        current_day = end_day  # Next segment's start day is the current segment's end day.
    return segments

def main():
    cities = list(city_durations.keys())
    valid_itinerary = None

    # Try every permutation of city order and pick the first that satisfies all constraints.
    for order in itertools.permutations(cities):
        # Must use only direct flights between consecutive cities.
        if not valid_flight_sequence(order):
            continue

        itinerary_segments = compute_itinerary(order, city_durations)
        # Although the sum is fixed, verify the total days match.
        if itinerary_segments[-1]["end_day"] != total_days:
            continue

        if not satisfies_special_constraints(itinerary_segments):
            continue

        # Found a valid itinerary!
        valid_itinerary = itinerary_segments
        break

    if valid_itinerary is None:
        output = {"itinerary": "No valid itinerary found"}
    else:
        # Build output structure with day_range strings.
        itinerary_output = []
        for seg in valid_itinerary:
            day_range = f"Day {seg['start_day']}-{seg['end_day']}"
            itinerary_output.append({"day_range": day_range, "place": seg["place"]})
        output = {"itinerary": itinerary_output}
    
    print(json.dumps(output))

if __name__ == '__main__':
    main()