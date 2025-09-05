import itertools
import json

def main():
    total_days = 12
    # Required days for each city
    required_days = {
        "Prague": 2,
        "Berlin": 3,
        "Tallinn": 5,
        "Stockholm": 5
    }
    # Conference in Berlin on these days
    conference_days = [6, 8]
    # Relatives visit in Tallinn between day 8 and day 12
    relatives_start = 8
    relatives_end = 12

    # Define direct flight connections (undirected)
    flights = {
        frozenset(["Berlin", "Tallinn"]),
        frozenset(["Prague", "Tallinn"]),
        frozenset(["Stockholm", "Tallinn"]),
        frozenset(["Prague", "Stockholm"]),
        frozenset(["Stockholm", "Berlin"])
    }

    cities = list(required_days.keys())
    valid_itinerary = None

    # Iterate over every permutation of the cities
    for perm in itertools.permutations(cities):
        # Check that every consecutive pair in the permutation is connected by a direct flight
        flight_possible = True
        for i in range(len(perm) - 1):
            if frozenset([perm[i], perm[i+1]]) not in flights:
                flight_possible = False
                break
        if not flight_possible:
            continue

        # Compute the itinerary segments with flight-day overlaps.
        # Rule: The first segment is assigned its full required days.
        # For every subsequent segment, the first day (flight day) is shared with the previous segment.
        segments = []
        current_day = 1
        for i, city in enumerate(perm):
            if i == 0:
                start_day = current_day
                end_day = start_day + required_days[city] - 1
                segments.append({"city": city, "start": start_day, "end": end_day})
                current_day = end_day  # next segment starts on the same day (flight overlap)
            else:
                start_day = current_day
                end_day = start_day + required_days[city] - 1
                segments.append({"city": city, "start": start_day, "end": end_day})
                current_day = end_day

        # Check that the total distinct days equal the trip length.
        if current_day != total_days:
            continue

        # Check that Berlin's segment covers the conference days.
        berlin_seg = next(seg for seg in segments if seg["city"] == "Berlin")
        if not (berlin_seg["start"] <= 6 <= berlin_seg["end"] and berlin_seg["start"] <= 8 <= berlin_seg["end"]):
            continue

        # Check that Tallinn's segment overlaps with the relatives visit period (day 8 to 12).
        tallinn_seg = next(seg for seg in segments if seg["city"] == "Tallinn")
        if not (tallinn_seg["end"] >= relatives_start and tallinn_seg["start"] <= relatives_end):
            continue

        # If all constraints are met, we select this itinerary.
        valid_itinerary = segments
        break

    # Format the itinerary output as a JSON dictionary.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for seg in valid_itinerary:
            day_range = f"Day {seg['start']}-{seg['end']}"
            itinerary_list.append({"day_range": day_range, "place": seg["city"]})
        result = {"itinerary": itinerary_list}

    print(json.dumps(result))

if __name__ == "__main__":
    main()