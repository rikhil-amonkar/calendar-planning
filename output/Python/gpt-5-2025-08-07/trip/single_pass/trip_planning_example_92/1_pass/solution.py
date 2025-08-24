import json
from itertools import permutations

def compute_itinerary(total_days, city_days, direct_flights):
    # Build directed adjacency from given flights
    adj = {c: set() for c in city_days}
    for a, b in direct_flights:
        if a not in adj:
            adj[a] = set()
        adj[a].add(b)

    cities = list(city_days.keys())
    n = len(cities)

    # Number of flights required to satisfy city-day totals with overlap rule
    required_flights = sum(city_days.values()) - total_days

    # For visiting all n cities exactly once, we must use n-1 flights
    if required_flights != n - 1:
        return {"itinerary": [], "note": "No feasible plan: required flights mismatch."}

    # Search for an ordering that forms a valid directed path
    for order in permutations(cities, n):
        # Check if consecutive edges exist
        valid_path = all(order[i+1] in adj.get(order[i], set()) for i in range(n - 1))
        if not valid_path:
            continue

        # Compute non-flight stays per city based on position in path
        pre_nonflight = []
        feasible = True
        for i, city in enumerate(order):
            d = city_days[city]
            if i == 0:         # first city: one flight day (leaving)
                pre = d - 1
            elif i == n - 1:   # last city: one flight day (arriving)
                pre = d - 1
            else:              # middle cities: two flight days (arriving + leaving)
                pre = d - 2
            if pre < 0:
                feasible = False
                break
            pre_nonflight.append(pre)
        if not feasible:
            continue

        # Build day ranges
        itinerary = []
        current_start = 1

        # First city: start at day 1, includes pre_nonflight[0] days and 1 flight day
        start_day = current_start
        end_day = start_day + pre_nonflight[0]  # includes flight day (leaving)
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": order[0]
        })

        # Middle cities (if any)
        for i in range(1, n - 1):
            start_day = end_day  # flight arrival day is shared
            end_day = start_day + pre_nonflight[i] + 1  # includes next flight day
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": order[i]
            })

        # Last city: includes arrival flight day + remaining pre_nonflight
        if n > 1:
            start_day = end_day  # arrival flight day shared
            end_day = start_day + pre_nonflight[-1]
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": order[-1]
            })

        # Validate final end day matches total trip days
        if end_day == total_days:
            return {"itinerary": itinerary}

    # If no path found
    return {"itinerary": [], "note": "No feasible itinerary with given constraints and direct flights."}


if __name__ == "__main__":
    # Input variables from the problem statement
    total_days = 12
    city_days = {
        "Riga": 5,
        "Vilnius": 7,
        "Dublin": 2
    }
    # Direct flights: "Dublin and Riga" (bidirectional), "from Riga to Vilnius" (directed)
    direct_flights = [
        ("Dublin", "Riga"),
        ("Riga", "Dublin"),
        ("Riga", "Vilnius")
    ]

    result = compute_itinerary(total_days, city_days, direct_flights)
    print(json.dumps(result, ensure_ascii=False))