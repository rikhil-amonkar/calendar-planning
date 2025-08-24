import itertools
import json

def compute_itinerary():
    # Input variables (constraints)
    total_days = 7
    cities = ["Madrid", "Dublin", "Tallinn"]
    stay_requirements = {
        "Madrid": 4,
        "Dublin": 3,
        "Tallinn": 2,
    }
    # Direct flights (bidirectional where applicable)
    direct_flights = {
        ("Madrid", "Dublin"),
        ("Dublin", "Madrid"),
        ("Dublin", "Tallinn"),
        ("Tallinn", "Dublin"),
    }
    workshop_city = "Tallinn"
    workshop_days = [6, 7]  # inclusive days the traveler must be in the workshop city

    # Basic validations
    assert set(stay_requirements.keys()) == set(cities), "Stay requirements must match the cities visited"
    transitions_needed = len(cities) - 1
    assert sum(stay_requirements.values()) == total_days + transitions_needed, (
        "Sum of stays must equal total days plus number of transitions (overlap on flight days)"
    )

    def valid_order(order):
        # Check direct flight feasibility
        for i in range(len(order) - 1):
            if (order[i], order[i + 1]) not in direct_flights:
                return False
        return True

    def build_schedule(order):
        # Compute inclusive start/end days for each city segment with overlaps on transition days
        s = {}
        e = {}
        # First city
        s[order[0]] = 1
        e[order[0]] = s[order[0]] + stay_requirements[order[0]] - 1
        # Subsequent cities
        for i in range(1, len(order)):
            prev, cur = order[i - 1], order[i]
            s[cur] = e[prev]  # travel day overlaps
            e[cur] = s[cur] + stay_requirements[cur] - 1
        return s, e

    def workshop_satisfied(s, e):
        if workshop_city not in s:
            return False
        return all(s[workshop_city] <= d <= e[workshop_city] for d in workshop_days)

    itinerary = None
    # Search over permutations to find a feasible itinerary
    for order in itertools.permutations(cities):
        if not valid_order(order):
            continue
        s, e = build_schedule(order)
        # Ensure the total spans exactly total_days and workshop constraint holds
        if e[order[-1]] != total_days:
            continue
        if not workshop_satisfied(s, e):
            continue
        # Build itinerary output
        itinerary = [{"day_range": f"Day {s[city]}-{e[city]}", "place": city} for city in order]
        break

    if itinerary is None:
        # Fallback: no valid plan (should not happen with given constraints)
        return {"itinerary": []}

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))