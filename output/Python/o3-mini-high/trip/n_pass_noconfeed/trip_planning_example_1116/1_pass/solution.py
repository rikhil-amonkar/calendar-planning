import itertools
import json

def main():
    # Total unique days for the trip
    total_unique_days = 20

    # Define required durations for each city (in "city-days")
    durations = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3
    }

    # Fixed event constraints:
    # - In Oslo: an annual show from day 16 to day 17 (requires being in Oslo on days 16 and 17).
    # - In Reykjavik: meet a friend between day 9 and day 13.
    # - In Munich: visit relatives between day 13 and day 16.
    # - In Frankfurt: attend a workshop from day 17 to day 20.
    #
    # Analysis shows that placing these four cities consecutively later in the itinerary,
    # with Reykjavik, then Munich, then Oslo, then Frankfurt, yields:
    # • Reykjavik (5 days) covering Day 9–13,
    # • Munich (4 days) covering Day 13–16,
    # • Oslo (2 days) covering Day 16–17, and
    # • Frankfurt (4 days) covering Day 17–20.
    #
    # The remaining four cities must come before these segments.
    fixed_chain = ["Reykjavik", "Munich", "Oslo", "Frankfurt"]

    # The remaining cities (non-fixed) are the ones not in the fixed chain.
    # Their durations are: Stockholm (4), Barcelona (3), Bucharest (2), Split (3)
    non_fixed = ["Stockholm", "Barcelona", "Bucharest", "Split"]

    # Direct flight connections (bidirectional)
    flights = set([
        frozenset(("Reykjavik", "Munich")),
        frozenset(("Munich", "Frankfurt")),
        frozenset(("Split", "Oslo")),
        frozenset(("Reykjavik", "Oslo")),
        frozenset(("Bucharest", "Munich")),
        frozenset(("Oslo", "Frankfurt")),
        frozenset(("Bucharest", "Barcelona")),
        frozenset(("Barcelona", "Frankfurt")),
        frozenset(("Reykjavik", "Frankfurt")),
        frozenset(("Barcelona", "Stockholm")),
        frozenset(("Barcelona", "Reykjavik")),
        frozenset(("Stockholm", "Reykjavik")),
        frozenset(("Barcelona", "Split")),
        frozenset(("Bucharest", "Oslo")),
        frozenset(("Bucharest", "Frankfurt")),
        frozenset(("Split", "Stockholm")),
        frozenset(("Barcelona", "Oslo")),
        frozenset(("Stockholm", "Munich")),
        frozenset(("Stockholm", "Oslo")),
        frozenset(("Split", "Frankfurt")),
        frozenset(("Barcelona", "Munich")),
        frozenset(("Stockholm", "Frankfurt")),
        frozenset(("Munich", "Oslo")),
        frozenset(("Split", "Munich"))
    ])

    def can_fly(city_a, city_b):
        return frozenset((city_a, city_b)) in flights

    # Given that each segment’s duration adds (duration - 1) unique days after the first,
    # the total city-days sum is sum(durations) = 27 and with 7 overlapping flight days,
    # the unique days count is 27 - 7 = 20.
    # To satisfy the friend meeting in Reykjavik between Day 9 and 13, the Reykjavik segment must start exactly on Day 9.
    # If we schedule the non-fixed cities as the first 4 segments, then:
    #   Unique start day for segment 1 is Day 1.
    #   For each subsequent segment, unique days add (duration - 1).
    # For the four non-fixed cities, the sum of (duration - 1) is:
    #   Stockholm: 4-1 = 3, Barcelona: 3-1 = 2, Bucharest: 2-1 = 1, Split: 3-1 = 2; total = 8.
    # Thus, Reykjavik (with 5 days) will start on Day 1 + 8 = Day 9, as required.
    #
    # We now search for an ordering of the non-fixed cities that is flight-feasible:
    valid_perm = None
    for perm in itertools.permutations(non_fixed):
        valid = True
        # Check consecutive flights among the non-fixed cities
        for i in range(len(perm) - 1):
            if not can_fly(perm[i], perm[i + 1]):
                valid = False
                break
        # Check direct flight from the last non-fixed city to Reykjavik (start of fixed chain)
        if valid and not can_fly(perm[-1], fixed_chain[0]):
            valid = False
        if valid:
            valid_perm = list(perm)
            break

    if valid_perm is None:
        result = {"itinerary": []}
    else:
        # Construct overall itinerary order: non-fixed (in found order) then fixed chain
        overall_order = valid_perm + fixed_chain

        # Each segment’s day range is computed as follows:
        # For the 1st city: Day 1 to (1 + duration - 1)
        # For subsequent cities: they start on the previous segment's end day (flight day overlap)
        itinerary = []
        current_day = 1
        for city in overall_order:
            duration = durations[city]
            start_day = current_day
            end_day = start_day + duration - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            current_day = end_day  # Next segment starts on the last day (flight overlap)
        result = {"itinerary": itinerary}

    print(json.dumps(result))

if __name__ == "__main__":
    main()