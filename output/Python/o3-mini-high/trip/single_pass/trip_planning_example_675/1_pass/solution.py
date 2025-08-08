#!/usr/bin/env python3
import json
import itertools

def main():
    # Input constraints as variables
    total_days = 16

    # Cities and their required durations
    durations = {
        "Dubrovnik": 4,
        "Split": 3,
        "Milan": 3,
        "Porto": 4,
        "Krakow": 2,
        "Munich": 5
    }

    # Direct flight connections represented as undirected edges (using frozenset)
    flight_edges = {
        frozenset({"Munich", "Porto"}),
        frozenset({"Split", "Milan"}),
        frozenset({"Milan", "Porto"}),
        frozenset({"Munich", "Krakow"}),
        frozenset({"Munich", "Milan"}),
        frozenset({"Dubrovnik", "Munich"}),
        frozenset({"Krakow", "Split"}),
        frozenset({"Krakow", "Milan"}),
        frozenset({"Munich", "Split"})
    }

    # Event constraints functions:
    # For Munich: must be attended from day 4 to day 8 (i.e. start day==4 and end day==8).
    # For Krakow: must meet friends between day 8 and day 9 (at least one of these days in the stay).
    # For Milan: wedding between day 11 and day 13 (at least one day in that range).
    def check_event(city, start, end):
        if city == "Munich":
            return (start == 4 and end == 8)
        elif city == "Krakow":
            # Overlap with [8,9]: valid if not (entire stay is before 8 or after 9)
            return not (end < 8 or start > 9)
        elif city == "Milan":
            # Overlap with [11,13]
            return not (end < 11 or start > 13)
        else:
            return True

    # Calculate the day ranges for the itinerary given an order.
    # According to the rule: 
    #   For the first city: days 1 to (duration)
    #   For every flight from city A to city B on the same day, that day is counted for both.
    # So for city i (i>=2), start day = previous segment's end day, end day = start day + (duration - 1)
    def compute_itinerary(order):
        itinerary = []
        current_day = 1
        for city in order:
            start_day = current_day
            end_day = start_day + durations[city] - 1
            itinerary.append((city, start_day, end_day))
            # Next segment starts on the same day the previous one ended (flight day overlap)
            current_day = end_day
        return itinerary

    # The required cities set
    all_cities = {"Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"}

    # According to the Munich show constraint, the traveler must be in Munich 
    # during days 4 to 8. Due to the flight overlapping rule, if Munich is the 2nd segment,
    # then start_day = (duration of first segment). For that to equal 4, the first segment 
    # must be 4 days long. So we force: order[0] must be a city with duration 4 ("Dubrovnik" or "Porto")
    # and order[1] must be "Munich".
    possible_first = [city for city in all_cities if durations[city] == 4]  # Dubrovnik or Porto

    valid_itinerary = None

    # Build itineraries: first city from possible_first, second city fixed to "Munich",
    # and the remaining four cities in any order.
    for first in possible_first:
        remaining = all_cities - {first, "Munich"}
        for perm in itertools.permutations(remaining):
            order = [first, "Munich"] + list(perm)
            # Compute the day ranges for each segment in this order.
            segments = compute_itinerary(order)
            # Safety check: last segment end day should equal total_days (always 21 - 5 = 16 if valid)
            if segments[-1][2] != total_days:
                continue

            # Check event constraints for relevant cities.
            event_ok = True
            for city, start, end in segments:
                if not check_event(city, start, end):
                    event_ok = False
                    break
            if not event_ok:
                continue

            # Check direct flight connectivity between consecutive cities.
            connectivity_ok = True
            for i in range(len(order)-1):
                if frozenset({order[i], order[i+1]}) not in flight_edges:
                    connectivity_ok = False
                    break
            if not connectivity_ok:
                continue

            # If all constraints are satisfied, choose this itinerary as valid.
            valid_itinerary = segments
            break
        if valid_itinerary is not None:
            break

    # If no valid itinerary was found, output an error JSON.
    if not valid_itinerary:
        result = {"error": "No valid itinerary found with given constraints."}
    else:
        # Build the final itinerary list in the desired JSON structure.
        itinerary_list = []
        for city, start, end in valid_itinerary:
            itinerary_list.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        result = {"itinerary": itinerary_list}

    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()