import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Total trip length
    total_days = 24

    # Cities and exact durations (in days)
    cities = [
        "Venice", "Reykjavik", "Munich", "Santorini", "Manchester",
        "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"
    ]
    durations = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5,
    }

    # Direct flight pairs (undirected)
    direct_flights_list = [
        ("Bucharest", "Manchester"),
        ("Munich", "Venice"),
        ("Santorini", "Manchester"),
        ("Vienna", "Reykjavik"),
        ("Venice", "Santorini"),
        ("Munich", "Porto"),
        ("Valencia", "Vienna"),
        ("Manchester", "Vienna"),
        ("Porto", "Vienna"),
        ("Venice", "Manchester"),
        ("Santorini", "Vienna"),
        ("Munich", "Manchester"),
        ("Munich", "Reykjavik"),
        ("Bucharest", "Valencia"),
        ("Venice", "Vienna"),
        ("Bucharest", "Vienna"),
        ("Porto", "Manchester"),
        ("Munich", "Vienna"),
        ("Valencia", "Porto"),
        ("Munich", "Bucharest"),
        ("Tallinn", "Munich"),
        ("Santorini", "Bucharest"),
        ("Munich", "Valencia"),
    ]
    # Convert to undirected set of frozensets
    direct_edges = set(frozenset(pair) for pair in direct_flights_list)

    # Fixed day windows (start day required)
    # Given exact durations and overlap rule, fixed day windows imply exact start days
    fixed_starts = {
        "Munich": 4,      # Day 4-6
        "Santorini": 8,   # Day 8-10
        "Valencia": 14,   # Day 14-15
    }

    # Set up constraint problem with position variables (1..10)
    problem = Problem()

    # Variables pos1..pos10 represent the city at each itinerary position
    pos_vars = [f"pos{i}" for i in range(1, 11)]
    for v in pos_vars:
        problem.addVariable(v, cities)

    # All positions must be distinct cities
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Adjacency must be connected by a direct flight
    def adjacent_direct(a, b):
        return frozenset([a, b]) in direct_edges

    for i in range(1, 10):
        problem.addConstraint(adjacent_direct, [f"pos{i}", f"pos{i+1}"])

    # Deductions from fixed days to prune search:
    # - Start day 1 city must end on day 4 to allow Munich to start on day 4 -> duration 4 -> Tallinn
    # - Therefore pos1 must be Tallinn, pos2 must be Munich (to start on day 4), and pos4 must be Santorini (to start on day 8)
    problem.addConstraint(lambda c: c == "Tallinn", ["pos1"])
    problem.addConstraint(lambda c: c == "Munich", ["pos2"])
    problem.addConstraint(lambda c: c == "Santorini", ["pos4"])

    # Global day schedule constraint: compute start/end days per position and enforce fixed start days and total end day
    def day_schedule_constraint(*order):
        # order corresponds to [pos1, pos2, ..., pos10]
        order = list(order)

        # Compute start and end days with overlap rule:
        # s1 = 1, e1 = 1 + d1 - 1
        # s_{i+1} = e_i, e_{i+1} = s_{i+1} + d_{i+1} - 1
        start_days = []
        end_days = []

        s = 1
        for i, city in enumerate(order):
            d = durations[city]
            e = s + d - 1
            start_days.append(s)
            end_days.append(e)
            s = e  # next start equals this end (overlap on travel day)

        # Total trip should end on day total_days
        if end_days[-1] != total_days:
            return False

        # Enforce fixed start days for specific cities
        city_to_start = {city: start_days[i] for i, city in enumerate(order)}
        for city, required_start in fixed_starts.items():
            if city_to_start.get(city) != required_start:
                return False

        # Verify total summed durations equals total_days + (num_cities - 1)
        # This is implied by the construction but we assert for safety
        if sum(durations[c] for c in cities) != total_days + (len(cities) - 1):
            return False

        return True

    problem.addConstraint(day_schedule_constraint, pos_vars)

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": [], "note": "No feasible itinerary found"}))
        return

    # Build the ordered list
    ordered_cities = [solution[f"pos{i}"] for i in range(1, 11)]

    # Compute day ranges
    itinerary = []
    current_start = 1
    for i, city in enumerate(ordered_cities):
        d = durations[city]
        end = current_start + d - 1
        itinerary.append({
            "day_range": f"Day {current_start}-{end}",
            "place": city
        })
        current_start = end  # next start equals this end (overlap on travel day)

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()