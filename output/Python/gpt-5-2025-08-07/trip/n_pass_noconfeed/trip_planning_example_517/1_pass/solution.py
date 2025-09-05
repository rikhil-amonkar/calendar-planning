import itertools
import json

def main():
    # Input variables (trip constraints)
    total_days = 19
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    desired_days = {
        "Dubrovnik": 5,
        "Warsaw": 2,
        "Stuttgart": 7,
        "Bucharest": 6,
        "Copenhagen": 3,
    }
    # Direct flight pairs (undirected)
    direct_flights = {
        ("Warsaw", "Copenhagen"),
        ("Stuttgart", "Copenhagen"),
        ("Warsaw", "Stuttgart"),
        ("Bucharest", "Copenhagen"),
        ("Bucharest", "Warsaw"),
        ("Copenhagen", "Dubrovnik"),
    }
    # Normalize to undirected lookup
    direct = set()
    for a, b in direct_flights:
        direct.add((a, b))
        direct.add((b, a))

    # Special constraints
    stuttgart_must_be_present_days = {7, 13}
    wedding_city = "Bucharest"
    wedding_window = (1, 6)  # inclusive

    # Helper functions
    def is_direct(a, b):
        return (a, b) in direct

    def compute_city_ranges(sequence):
        """
        Compute per-city day ranges with overlap on transition days.
        If moving from city A to B occurs on day X, that day is counted for both A and B,
        which is modeled by making the next city's start equal to the previous city's end.
        """
        ranges = {}
        current_start = 1
        for i, city in enumerate(sequence):
            if i == 0:
                start = 1
            else:
                prev_city = sequence[i - 1]
                # Overlap: next city starts on the previous city's end day
                start = ranges[prev_city][1]
            end = start + desired_days[city] - 1
            ranges[city] = (start, end)
        return ranges

    def validate(sequence, ranges):
        # Check direct-flight feasibility between consecutive cities
        for i in range(1, len(sequence)):
            if not is_direct(sequence[i - 1], sequence[i]):
                return False

        # Check total trip days align
        trip_end = ranges[sequence[-1]][1]
        if trip_end != total_days:
            return False

        # Stuttgart day constraints
        if "Stuttgart" not in ranges:
            return False
        s_start, s_end = ranges["Stuttgart"]
        for day in stuttgart_must_be_present_days:
            if not (s_start <= day <= s_end):
                return False

        # Wedding presence in Bucharest within window (at least one day inside)
        if wedding_city not in ranges:
            return False
        b_start, b_end = ranges[wedding_city]
        w_start, w_end = wedding_window
        if not (b_start <= w_end and b_end >= w_start):
            return False

        # Ensure Dubrovnik has a neighbor that is Copenhagen (since only direct link)
        # In a path of unique cities, Dubrovnik must be at an end with Copenhagen adjacent.
        dub_index = sequence.index("Dubrovnik")
        if dub_index == 0:
            # Must be adjacent to Copenhagen as the next city
            if len(sequence) < 2 or sequence[1] != "Copenhagen":
                return False
        elif dub_index == len(sequence) - 1:
            # Must be adjacent to Copenhagen as the previous city
            if len(sequence) < 2 or sequence[-2] != "Copenhagen":
                return False
        else:
            # If in the middle, both neighbors must be Copenhagen, which is impossible without duplicates
            return False

        # Ensure the per-city day counts match desired exactly
        for city in cities:
            start, end = ranges[city]
            if (end - start + 1) != desired_days[city]:
                return False

        # Ensure the number of flights equals n_cities - 1 and the "overlap" math works
        flights = len(sequence) - 1
        if sum(desired_days[c] for c in sequence) - flights != total_days:
            return False

        # Ensure Day 1 is within the first city's range (trivially true by construction)
        if ranges[sequence[0]][0] != 1:
            return False

        return True

    # Search for a valid itinerary
    valid_itinerary = None
    # Try all permutations; optimize by insisting Dubrovnik be at an end due to connectivity
    middle_cities = [c for c in cities if c != "Dubrovnik"]
    for dub_at_end in ["front", "back"]:
        if dub_at_end == "front":
            # Dubrovnik must be first and second must be Copenhagen (connectivity), but wedding constraint likely fails
            for perm in itertools.permutations(middle_cities):
                sequence = ["Dubrovnik"] + list(perm)
                # Quick neighbor check for Dubrovnik adjacency
                if len(sequence) < 2 or sequence[1] != "Copenhagen":
                    continue
                ranges = compute_city_ranges(sequence)
                if validate(sequence, ranges):
                    valid_itinerary = sequence, ranges
                    break
        else:
            # Dubrovnik at the end and previous must be Copenhagen
            for perm in itertools.permutations(middle_cities):
                sequence = list(perm) + ["Dubrovnik"]
                if len(sequence) < 2 or sequence[-2] != "Copenhagen":
                    continue
                ranges = compute_city_ranges(sequence)
                if validate(sequence, ranges):
                    valid_itinerary = sequence, ranges
                    break
        if valid_itinerary:
            break

    # Prepare output
    if valid_itinerary:
        sequence, ranges = valid_itinerary
        itinerary = []
        for city in sequence:
            start, end = ranges[city]
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))
    else:
        # Fallback if no valid itinerary found
        print(json.dumps({"itinerary": [], "message": "No valid itinerary found for given constraints."}, ensure_ascii=False))

if __name__ == "__main__":
    main()