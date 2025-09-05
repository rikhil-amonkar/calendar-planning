import json
import itertools

def compute_itinerary(total_days, required_stays, direct_flights):
    cities = list(required_stays.keys())
    n = len(cities)
    sum_stays = sum(required_stays.values())
    flights_needed = sum_stays - total_days

    # Build directed adjacency set
    adj = set(direct_flights)

    # We aim to visit each city once; minimal flights to connect n cities in a path is n-1
    if flights_needed != n - 1:
        raise ValueError("Infeasible: flights needed does not match visits. flights_needed={}, n-1={}".format(flights_needed, n-1))

    def valid_path(order):
        # Check directed connectivity along the path
        for i in range(len(order) - 1):
            if (order[i], order[i+1]) not in adj:
                return False
        return True

    def build_itinerary_from_order(order):
        # Compute pure days for each city based on position in path
        pure_days = []
        for idx, city in enumerate(order):
            if idx == 0:
                overlaps = 1  # first city has 1 flight day included
            elif idx == len(order) - 1:
                overlaps = 1  # last city has 1 flight day included
            else:
                overlaps = 2  # middle city has 2 flight days included
            pd = required_stays[city] - overlaps
            if pd < 0:
                return None
            pure_days.append(pd)

        # Build day ranges including overlap on flight days
        itinerary = []
        pos = 1  # current day pointer
        for idx, city in enumerate(order):
            if idx == 0:
                start = pos
                end = pos + pure_days[idx]  # includes first flight day
                pos = end  # next city starts on the flight day (overlap)
            elif idx == len(order) - 1:
                start = pos  # starts on previous flight day
                end = pos + pure_days[idx]  # no flight after last city
            else:
                start = pos  # starts on previous flight day
                end = pos + pure_days[idx] + 1  # includes next flight day
                pos = end  # next city starts on this flight day

            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })

        # Validate total days align
        last_end = itinerary[-1]["day_range"].split("-")[-1]
        last_end_day = int(last_end)
        if last_end_day != total_days:
            return None

        return itinerary

    # Try all permutations to find a valid itinerary
    for order in itertools.permutations(cities):
        if not valid_path(order):
            continue
        itinerary = build_itinerary_from_order(order)
        if itinerary is not None:
            return {"itinerary": itinerary}

    raise ValueError("No valid itinerary found under the given constraints.")

if __name__ == "__main__":
    # Input variables based on provided constraints
    total_days = 12
    required_stays = {
        "Riga": 5,
        "Vilnius": 7,
        "Dublin": 2
    }
    # Direct flights: "Dublin and Riga" implies bidirectional; "from Riga to Vilnius" is directed
    direct_flights = [
        ("Dublin", "Riga"),
        ("Riga", "Dublin"),
        ("Riga", "Vilnius")
    ]

    result = compute_itinerary(total_days, required_stays, direct_flights)
    print(json.dumps(result, ensure_ascii=False))