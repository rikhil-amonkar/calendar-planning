import json
import itertools

# Define the city durations and flight connections.
cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
durations = {
    "Reykjavik": 7,
    "Riga": 2,
    "Warsaw": 3,
    "Istanbul": 6,
    "Krakow": 7
}

# Flight connections (bidirectional)
flights = {
    "Istanbul": {"Krakow", "Warsaw", "Riga"},
    "Krakow": {"Istanbul", "Warsaw"},
    "Warsaw": {"Reykjavik", "Istanbul", "Krakow", "Riga"},
    "Riga": {"Istanbul", "Warsaw"},
    "Reykjavik": {"Warsaw"}
}

# Function to compute the timeline for an itinerary.
# Note: If you fly from city A to city B on day X, then day X counts for both cities.
def compute_timeline(itinerary, durations):
    timeline = []
    current_day = 1
    for city in itinerary:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        timeline.append((start_day, end_day))
        # The next city begins on the same day as the current city's last day (flight day overlap)
        current_day = end_day
    return timeline

# Check if the candidate itinerary meets connectivity and time-specific constraints.
def is_valid_itinerary(itinerary, durations, flights):
    # Check direct flight connectivity for each consecutive pair
    for i in range(len(itinerary) - 1):
        if itinerary[i+1] not in flights[itinerary[i]]:
            return False

    timeline = compute_timeline(itinerary, durations)
    
    # Total trip days must equal 21 (automatically satisfied if durations sum minus overlaps equals 21)
    if timeline[-1][1] != 21:
        return False

    # Constraint 1: Meet friend in Riga between day 1 and day 2
    if "Riga" in itinerary:
        riga_index = itinerary.index("Riga")
        riga_start, riga_end = timeline[riga_index]
        # The friend meeting must occur on day 1 or day 2, so Riga must start by day 2.
        if riga_start > 2:
            return False
    else:
        return False

    # Constraint 2: Attend wedding in Istanbul between day 2 and day 7.
    if "Istanbul" in itinerary:
        istanbul_index = itinerary.index("Istanbul")
        istanbul_start, istanbul_end = timeline[istanbul_index]
        # The Istanbul stay must overlap with days 2 to 7.
        if istanbul_start > 7 or istanbul_end < 2:
            return False
    else:
        return False

    return True

def main():
    valid_itinerary = None
    valid_timeline = None

    # Try all permutations and select the first itinerary that meets all constraints.
    for perm in itertools.permutations(cities):
        itinerary = list(perm)
        if is_valid_itinerary(itinerary, durations, flights):
            valid_itinerary = itinerary
            valid_timeline = compute_timeline(itinerary, durations)
            break

    if valid_itinerary is None:
        result = {"error": "No valid itinerary found"}
    else:
        itinerary_output = []
        # Prepare the output with day-range and place information.
        for city, (start, end) in zip(valid_itinerary, valid_timeline):
            day_range = f"Day {start}-{end}"
            itinerary_output.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_output}

    print(json.dumps(result))

if __name__ == "__main__":
    main()