import json
from constraint import Problem, AllDifferentConstraint

def build_itinerary():
    # Cities to visit (exactly 10)
    cities = [
        "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw",
        "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]

    # Duration requirements (inclusive of both start and end days)
    durations = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }

    # Fixed start-day requirements due to events:
    # - Edinburgh friend meet: days 1-5 -> Edinburgh must be days 1-5
    # - Budapest annual show: days 9-13 -> Budapest must be days 9-13
    # - Stockholm friends tour: days 17-18 -> Stockholm must be days 17-18
    # - Munich workshop: days 18-20 -> Munich must be days 18-20
    # - Warsaw conference: days 25-29 -> Warsaw must be days 25-29
    fixed_starts = {
        "Edinburgh": 1,
        "Budapest": 9,
        "Stockholm": 17,
        "Munich": 18,
        "Warsaw": 25
    }

    # Direct flights list. "A and B" means both directions, "from A to B" is one-way.
    undirected_pairs = [
        ("Budapest", "Munich"),
        ("Bucharest", "Riga"),
        ("Munich", "Krakow"),
        ("Munich", "Warsaw"),
        ("Munich", "Bucharest"),
        ("Edinburgh", "Stockholm"),
        ("Barcelona", "Warsaw"),
        ("Edinburgh", "Krakow"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Krakow"),
        ("Budapest", "Vienna"),
        ("Barcelona", "Stockholm"),
        ("Stockholm", "Munich"),
        ("Edinburgh", "Budapest"),
        ("Barcelona", "Riga"),
        ("Edinburgh", "Barcelona"),
        ("Vienna", "Riga"),
        ("Barcelona", "Budapest"),
        ("Bucharest", "Warsaw"),
        ("Vienna", "Krakow"),
        ("Edinburgh", "Munich"),
        ("Barcelona", "Bucharest"),
        ("Edinburgh", "Riga"),
        ("Vienna", "Stockholm"),
        ("Warsaw", "Krakow"),
        ("Barcelona", "Krakow"),
        ("Vienna", "Bucharest"),
        ("Budapest", "Warsaw"),
        ("Vienna", "Warsaw"),
        ("Barcelona", "Vienna"),
        ("Budapest", "Bucharest"),
        ("Vienna", "Munich"),
        ("Riga", "Warsaw"),
        ("Stockholm", "Riga"),
        ("Stockholm", "Warsaw")
    ]
    directed_pairs = [
        ("Riga", "Munich")  # one-way
    ]

    # Build directed edge set for flight validity check
    flights = set()
    for a, b in undirected_pairs:
        flights.add((a, b))
        flights.add((b, a))
    for a, b in directed_pairs:
        flights.add((a, b))

    # Total trip length
    total_days = 32
    num_cities = len(cities)

    problem = Problem()

    # Variables for sequence positions and start days
    # P1..P10 are cities at positions 1..10 (a permutation of all cities)
    # S1..S10 are the start days of the city at that position
    pos_vars = [f"P{i}" for i in range(1, num_cities + 1)]
    start_vars = [f"S{i}" for i in range(1, num_cities + 1)]

    # Domains
    for pv in pos_vars:
        problem.addVariable(pv, cities)
    for sv in start_vars:
        problem.addVariable(sv, range(1, total_days + 1))

    # All city positions must be a permutation (each city exactly once)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # The first segment must start on day 1
    problem.addConstraint(lambda s: s == 1, ["S1"])

    # Last segment must end on day 32
    def last_end_is_total(c, s):
        return s + durations[c] - 1 == total_days
    problem.addConstraint(last_end_is_total, ["P10", "S10"])

    # For each position, enforce fixed start days if that city has one
    for i in range(1, num_cities + 1):
        def fixed_start_constraint(city, s, fixed=fixed_starts):
            if city in fixed:
                return s == fixed[city]
            return True
        problem.addConstraint(fixed_start_constraint, [f"P{i}", f"S{i}"])

    # Transition constraints:
    # - Direct flight from Pk to Pk+1 must exist
    # - Next start day equals current end day (overlap on travel day)
    for i in range(1, num_cities):
        def transition(c1, s1, c2, s2, durs=durations, fl=flights):
            # Ensure direct flight exists from c1 to c2
            if (c1, c2) not in fl:
                return False
            # Ensure overlapping day rule
            return s2 == s1 + durs[c1] - 1
        problem.addConstraint(transition, [f"P{i}", f"S{i}", f"P{i+1}", f"S{i+1}"])

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    # Choose the first solution
    sol = solutions[0]

    # Build itinerary as ordered list
    itinerary = []
    for i in range(1, num_cities + 1):
        city = sol[f"P{i}"]
        start_day = sol[f"S{i}"]
        end_day = start_day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = build_itinerary()
    print(json.dumps(result))