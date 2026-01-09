import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and required presence days
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    required_days = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4,
    }

    # Direct flight pairs (treated as undirected)
    direct_pairs = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius"),
    ]
    # Build undirected set
    flights = set()
    for a, b in direct_pairs:
        flights.add(frozenset((a, b)))

    # Helper to compute block lengths given an order
    def compute_lengths(order):
        lengths = []
        for i, city in enumerate(order):
            if i < len(order) - 1:
                L = required_days[city] - 1
            else:
                L = required_days[city]
            if L <= 0:
                return None
            lengths.append(L)
        if sum(lengths) != 15:
            return None
        return lengths

    # Build CSP
    problem = Problem()
    pos_vars = [f"P{i}" for i in range(1, 8)]
    for var in pos_vars:
        problem.addVariable(var, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Adjacency (direct flights) constraint
    def adjacency_ok(*args):
        order = list(args)
        for i in range(len(order) - 1):
            if frozenset((order[i], order[i + 1])) not in flights:
                return False
        return True

    problem.addConstraint(adjacency_ok, pos_vars)

    # Event and presence constraints
    def events_and_presence(*args):
        order = list(args)
        lengths = compute_lengths(order)
        if lengths is None:
            return False

        # Build presence sets per city
        presence = {c: set() for c in cities}
        day = 1
        for i, city in enumerate(order):
            L = lengths[i]
            # Days assigned to this city (end-of-day location)
            for j in range(L):
                presence[city].add(day + j)
            # Travel day to next city counts for origin city also
            if i < len(order) - 1:
                presence[city].add(day + L)  # first day of next block
            day += L

        # Ensure presence counts match required days
        for c in cities:
            if len(presence[c]) != required_days[c]:
                return False

        # Meeting in Amsterdam between day 2 and 3
        if not ({2, 3} & presence["Amsterdam"]):
            return False

        # Workshop in Vilnius between day 7 and 11
        if not (set(range(7, 12)) & presence["Vilnius"]):
            return False

        # Wedding in Stockholm between day 13 and 15
        if not (set(range(13, 16)) & presence["Stockholm"]):
            return False

        return True

    problem.addConstraint(events_and_presence, pos_vars)

    # Solve
    solution = problem.getSolution()
    if not solution:
        # Fallback JSON in case no feasible solution found
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Extract order in positions P1..P7
    order = [solution[f"P{i}"] for i in range(1, 8)]
    lengths = compute_lengths(order)

    # Build itinerary as day ranges
    itinerary = []
    current_day = 1
    for city, L in zip(order, lengths):
        start = current_day
        end = current_day + L - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        current_day = end + 1

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()