import itertools
import json

def main():
    total_days = 17
    start_city = "Warsaw"
    other_cities = ["Budapest", "Paris", "Riga"]
    required_days = {
        "Warsaw": 2,
        "Budapest": 7,
        "Paris": 4,
        "Riga": 7
    }
    direct_flights = {
        "Warsaw": ["Budapest", "Riga", "Paris"],
        "Budapest": ["Warsaw", "Paris"],
        "Paris": ["Budapest", "Warsaw", "Riga"],
        "Riga": ["Warsaw", "Paris"]
    }
    wedding_start = 11
    wedding_end = 17

    L1 = 2  # leave Warsaw on day 2

    cases = [
        (4, 7, 7),
        (7, 4, 7),
        (7, 7, 4)
    ]

    perms = list(itertools.permutations(other_cities))
    solution_found = False
    result_itinerary = None

    for perm in perms:
        for case in cases:
            d2, d3, d4 = case
            c2, c3, c4 = perm

            L2 = d2 + 1
            L3 = L2 + d3 - 1

            if d4 != (18 - L3):
                continue

            if required_days[c2] != d2:
                continue
            if required_days[c3] != d3:
                continue
            if required_days[c4] != d4:
                continue

            if c2 not in direct_flights[start_city]:
                continue
            if c3 not in direct_flights[c2]:
                continue
            if c4 not in direct_flights[c3]:
                continue

            riga_segment = None
            if c2 == "Riga":
                riga_segment = 2
            elif c3 == "Riga":
                riga_segment = 3
            elif c4 == "Riga":
                riga_segment = 4

            if riga_segment is None:
                continue

            valid_riga = False
            if riga_segment == 2:
                if L2 >= wedding_start:
                    valid_riga = True
            elif riga_segment == 3:
                if L3 >= wedding_start:
                    valid_riga = True
            else:
                valid_riga = True

            if not valid_riga:
                continue

            itinerary = [
                {"day_range": f"Day 1-{L1}", "place": start_city},
                {"day_range": f"Day {L1}-{L2}", "place": c2},
                {"day_range": f"Day {L2}-{L3}", "place": c3},
                {"day_range": f"Day {L3}-17", "place": c4}
            ]
            result_itinerary = itinerary
            solution_found = True
            break
        if solution_found:
            break

    if not solution_found:
        result_itinerary = []

    print(json.dumps({"itinerary": result_itinerary}))

if __name__ == "__main__":
    main()