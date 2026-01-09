import json
from constraint import Problem

def main():
    # Input variables (trip constraints)
    total_days = 15
    city_durations = {
        "Stuttgart": 6,
        "Seville": 7,
        "Manchester": 4,
    }
    # Direct flight pairs (undirected)
    direct_flights = {
        frozenset(["Manchester", "Seville"]),
        frozenset(["Stuttgart", "Manchester"]),
    }

    # Allowed sequences must respect direct flights between consecutive cities
    candidate_orders = [
        ("Seville", "Manchester", "Stuttgart"),
        ("Stuttgart", "Manchester", "Seville"),
    ]

    def is_connected(order):
        return all(frozenset([order[i], order[i+1]]) in direct_flights for i in range(len(order)-1))

    # Set up the constraint problem
    problem = Problem()
    problem.addVariable("order", candidate_orders)
    # Start days of each segment in the chosen order (start1 is fixed to Day 1)
    problem.addVariable("s1", [1])
    problem.addVariable("s2", range(1, total_days + 1))
    problem.addVariable("s3", range(1, total_days + 1))

    # Constraint: order must be connected by direct flights
    def direct_flight_constraint(order):
        return is_connected(order)
    problem.addConstraint(direct_flight_constraint, ["order"])

    # Constraints linking segment start days given durations and 1-day overlap when flying
    def segment_alignment(order, s1, s2, s3):
        d1 = city_durations[order[0]]
        d2 = city_durations[order[1]]
        d3 = city_durations[order[2]]

        # s2 is the flight day from segment 1 to 2 (overlap day)
        # s3 is the flight day from segment 2 to 3 (overlap day)
        # End of third segment should be day total_days
        # end3 = s3 + d3 - 1
        return (s2 == s1 + d1 - 1) and (s3 == s2 + d2 - 1) and (s3 + d3 - 1 == total_days)
    problem.addConstraint(segment_alignment, ["order", "s1", "s2", "s3"])

    # Constraint: meet a friend in Stuttgart between day 1 and day 6 (inclusive)
    # This means Stuttgart's stay must include at least one day in [1,6].
    def stuttgart_meet_constraint(order, s1, s2, s3):
        # Determine start day of Stuttgart based on position in order
        if order[0] == "Stuttgart":
            st_start = s1
        elif order[1] == "Stuttgart":
            st_start = s2
        else:
            st_start = s3

        st_end = st_start + city_durations["Stuttgart"] - 1
        # Check overlap with [1,6]
        return not (st_end < 1 or st_start > 6)
    problem.addConstraint(stuttgart_meet_constraint, ["order", "s1", "s2", "s3"])

    solutions = problem.getSolutions()

    # If multiple solutions exist, pick one with earliest Stuttgart day (then lexicographically)
    chosen = None
    if solutions:
        def key_fn(sol):
            order = sol["order"]
            s1, s2, s3 = sol["s1"], sol["s2"], sol["s3"]
            if order[0] == "Stuttgart":
                st_start = s1
            elif order[1] == "Stuttgart":
                st_start = s2
            else:
                st_start = s3
            return (st_start, order)
        chosen = sorted(solutions, key=key_fn)[0]

    # Build the itinerary output
    if chosen:
        order = chosen["order"]
        s1, s2, s3 = chosen["s1"], chosen["s2"], chosen["s3"]
        starts = [s1, s2, s3]
        itinerary = []
        for i, city in enumerate(order):
            start_day = starts[i]
            end_day = start_day + city_durations[city] - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()