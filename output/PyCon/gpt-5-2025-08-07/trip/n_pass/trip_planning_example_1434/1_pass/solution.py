import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required durations (days)
    durations = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5
    }

    total_days = 23
    cities = list(durations.keys())

    # Direct flights (undirected)
    direct_pairs = [
        ("Rome", "Stuttgart"),
        ("Venice", "Rome"),
        ("Dublin", "Bucharest"),
        ("Mykonos", "Rome"),
        ("Seville", "Lisbon"),
        ("Frankfurt", "Venice"),
        ("Venice", "Stuttgart"),
        ("Bucharest", "Lisbon"),
        ("Nice", "Mykonos"),
        ("Venice", "Lisbon"),
        ("Dublin", "Lisbon"),
        ("Venice", "Dublin"),
        ("Rome", "Seville"),
        ("Frankfurt", "Rome"),
        ("Nice", "Dublin"),
        ("Rome", "Bucharest"),
        ("Frankfurt", "Dublin"),
        ("Rome", "Dublin"),
        ("Venice", "Dublin"),
        ("Rome", "Lisbon"),
        ("Frankfurt", "Lisbon"),
        ("Nice", "Rome"),
        ("Frankfurt", "Nice"),
        ("Frankfurt", "Stuttgart"),
        ("Frankfurt", "Bucharest"),
        ("Lisbon", "Stuttgart"),
        ("Nice", "Lisbon"),
        ("Seville", "Dublin"),
    ]
    adjacency = set(frozenset(pair) for pair in direct_pairs)

    # Helper to compute starts/ends from an ordered list of cities
    def compute_schedule(order):
        starts = {}
        ends = {}
        s = 1
        for city in order:
            L = durations[city]
            starts[city] = s
            e = s + L - 1
            ends[city] = e
            s = e  # next start overlaps on the flight day
        return starts, ends

    # Setup CSP
    problem = Problem()
    # Variables: position of each city in the sequence (1..10)
    for c in cities:
        problem.addVariable(c, range(1, len(cities) + 1))
    problem.addConstraint(AllDifferentConstraint())

    # Frankfurt must start Day 1 (to attend a wedding between day 1 and 5 and has 5 days)
    problem.addConstraint(lambda p: p == 1, ("Frankfurt",))

    # For any pair of cities without a direct flight, they cannot be consecutive
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            a, b = cities[i], cities[j]
            if frozenset((a, b)) not in adjacency:
                problem.addConstraint(lambda pa, pb: abs(pa - pb) != 1, (a, b))

    # Global constraint to enforce day windows and adjacency along the sequence
    def global_constraint(*vals):
        assignment = dict(zip(cities, vals))
        # Allow partial assignments
        if any(v is None for v in assignment.values()):
            return True

        # Build sequence by position
        try:
            seq = sorted(cities, key=lambda c: assignment[c])
        except KeyError:
            return True

        # Ensure consecutive pairs are directly connected
        for i in range(len(seq) - 1):
            a, b = seq[i], seq[i + 1]
            if frozenset((a, b)) not in adjacency:
                return False

        # Compute schedule
        starts, ends = compute_schedule(seq)

        # Ensure total coverage ends at Day 23
        if ends[seq[-1]] != total_days:
            return False

        # Mykonos must be exactly on days 10-11 (meet friends between day 10 and 11)
        if not (starts["Mykonos"] == 10 and ends["Mykonos"] == 11):
            return False

        # Seville conference requires being there days 13 and 17; with 5 days, it must be 13-17
        if not (starts["Seville"] == 13 and ends["Seville"] == 17):
            return False

        # Frankfurt 5 days including days 1-5; as first city, this enforces 1-5
        if not (starts["Frankfurt"] == 1 and ends["Frankfurt"] == 5):
            return False

        # All city durations already enforced by construction; nothing else to check
        return True

    problem.addConstraint(global_constraint, tuple(cities))

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary output
    seq = sorted(cities, key=lambda c: solution[c])
    starts, ends = compute_schedule(seq)
    itinerary = []
    for city in seq:
        itinerary.append({
            "day_range": f"Day {starts[city]}-{ends[city]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()