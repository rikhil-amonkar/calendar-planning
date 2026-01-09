import json
from constraint import Problem

def main():
    # Input variables / constraints
    total_days = 9
    cities = ["Mykonos", "Budapest", "Hamburg"]
    required_stays = {
        "Mykonos": 6,
        "Budapest": 3,
        "Hamburg": 2
    }
    conference_days_mykonos = {4, 9}
    direct_flights = {
        ("Budapest", "Mykonos"), ("Mykonos", "Budapest"),
        ("Hamburg", "Budapest"), ("Budapest", "Hamburg")
    }

    # Derived requirement: number of transitions needed so that summed stays match,
    # given flight days count for both origin and destination.
    required_transitions = sum(required_stays.values()) - total_days
    if required_transitions < 0 or required_transitions > (total_days - 1):
        raise ValueError("Infeasible input constraints: transitions requirement is invalid.")

    # Set up CSP
    prob = Problem()
    day_vars = [f"D{d}" for d in range(1, total_days + 1)]
    for dv in day_vars:
        prob.addVariable(dv, cities)

    # Must be in Mykonos on conference days
    for d in conference_days_mykonos:
        prob.addConstraint(lambda c: c == "Mykonos", [f"D{d}"])

    # Global constraint enforcing direct flights, transitions count, and stay counts (with travel double-counting)
    def itinerary_constraint(*vals):
        # vals is ordered as D1, D2, ..., D9
        # Check allowed transitions (direct flights only when city changes)
        transitions = 0
        for i in range(1, total_days):
            prev_city = vals[i - 1]
            curr_city = vals[i]
            if prev_city != curr_city:
                if (prev_city, curr_city) not in direct_flights:
                    return False
                transitions += 1

        if transitions != required_transitions:
            return False

        # Count stays with rule: if flying from A to B on day X, day X counts for both A and B
        counts = {c: 0 for c in cities}
        # Base count: each day counts for the city you are in that day
        for i in range(total_days):
            counts[vals[i]] += 1
        # Add previous city on change days
        for i in range(1, total_days):
            if vals[i] != vals[i - 1]:
                counts[vals[i - 1]] += 1

        # Enforce required stays
        for c in required_stays:
            if counts[c] != required_stays[c]:
                return False

        # Ensure all three cities are visited (implied by required_stays > 0, but keep explicit)
        if len({v for v in vals}) != 3:
            return False

        # Also ensure Mykonos explicitly includes the conference days (redundant with earlier constraint)
        if vals[3] != "Mykonos" or vals[8] != "Mykonos":
            return False

        return True

    prob.addConstraint(itinerary_constraint, day_vars)

    solutions = prob.getSolutions()
    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    # Choose the first solution deterministically (solutions are dictionaries)
    sol = solutions[0]
    days_ordered = [(d, sol[f"D{d}"]) for d in range(1, total_days + 1)]

    # Build condensed itinerary as contiguous segments by city
    itinerary = []
    start = 1
    current_city = days_ordered[0][1]
    for day in range(2, total_days + 1):
        city = days_ordered[day - 1][1]
        if city != current_city:
            itinerary.append({"day_range": f"Day {start}-{day - 1}", "place": current_city})
            start = day
            current_city = city
    # Append last segment
    itinerary.append({"day_range": f"Day {start}-{total_days}", "place": current_city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()