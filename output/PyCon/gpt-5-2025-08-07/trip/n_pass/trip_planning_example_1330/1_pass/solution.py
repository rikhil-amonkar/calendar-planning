import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Cities and durations (days)
    cities = ["Salzburg", "Hamburg", "Venice", "Nice", "Zurich", "Bucharest", "Copenhagen", "Brussels", "Naples"]
    duration = {
        "Salzburg": 2,
        "Venice": 5,
        "Bucharest": 4,
        "Brussels": 2,
        "Hamburg": 4,
        "Copenhagen": 4,
        "Nice": 3,
        "Zurich": 5,
        "Naples": 4,
    }
    total_days = 25
    n = len(cities)

    # Direct flight connections (undirected)
    direct_pairs = [
        ("Zurich", "Brussels"),
        ("Bucharest", "Copenhagen"),
        ("Venice", "Brussels"),
        ("Nice", "Zurich"),
        ("Hamburg", "Nice"),
        ("Zurich", "Naples"),
        ("Hamburg", "Bucharest"),
        ("Zurich", "Copenhagen"),
        ("Bucharest", "Brussels"),
        ("Hamburg", "Brussels"),
        ("Venice", "Naples"),
        ("Venice", "Copenhagen"),
        ("Bucharest", "Naples"),
        ("Hamburg", "Copenhagen"),
        ("Venice", "Zurich"),
        ("Nice", "Brussels"),
        ("Hamburg", "Venice"),
        ("Copenhagen", "Naples"),
        ("Nice", "Naples"),
        ("Hamburg", "Zurich"),
        ("Salzburg", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Brussels", "Naples"),
        ("Copenhagen", "Brussels"),
        ("Venice", "Nice"),
        ("Nice", "Copenhagen"),
    ]
    adjacency = set(frozenset(pair) for pair in direct_pairs)

    # Fixed windows (must be in city on these precise start days due to exact lengths)
    fixed_starts = {
        "Nice": 9,           # visit relatives between day 9 and 11, length 3 -> start=9
        "Copenhagen": 18,    # wedding between day 18 and 21, length 4 -> start=18
        "Brussels": 21,      # meet friends between day 21 and 22, length 2 -> start=21
        "Naples": 22,        # workshop between day 22 and 25, length 4 -> start=22
    }

    problem = Problem()

    # Variables: position in itinerary (1..n) and start day (1..25)
    for c in cities:
        problem.addVariable(f"pos_{c}", range(1, n + 1))
        problem.addVariable(f"S_{c}", range(1, total_days + 1))

    # All positions must be distinct
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{c}" for c in cities])

    # Fixed start day constraints for specific cities
    for c, s in fixed_starts.items():
        problem.addConstraint(lambda val, s=s: val == s, [f"S_{c}"])

    # Start city must start on day 1; end city must end on day total_days
    for c in cities:
        # If pos==1 then S==1
        problem.addConstraint(
            lambda pos, s: (s == 1) if pos == 1 else True,
            [f"pos_{c}", f"S_{c}"]
        )
        # If pos==n then S + dur - 1 == total_days
        problem.addConstraint(
            lambda pos, s, d=duration[c], total_days=total_days: (s + d - 1 == total_days) if pos == n else True,
            [f"pos_{c}", f"S_{c}"]
        )

    # Consecutive day linking: if city B follows city A then S_B == S_A + dur_A - 1 (shared transition day)
    for a in cities:
        for b in cities:
            if a == b:
                continue
            problem.addConstraint(
                lambda pos_a, pos_b, s_a, s_b, d_a=duration[a]: True if pos_b != pos_a + 1 else (s_b == s_a + d_a - 1),
                [f"pos_{a}", f"pos_{b}", f"S_{a}", f"S_{b}"]
            )

    # Direct flights between consecutive cities
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            a, b = cities[i], cities[j]
            problem.addConstraint(
                lambda pos_a, pos_b, a=a, b=b, adj=adjacency: True if abs(pos_a - pos_b) != 1 else (frozenset((a, b)) in adj),
                [f"pos_{a}", f"pos_{b}"]
            )

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary
    itinerary = []
    # Sort cities by their position
    ordered = sorted(cities, key=lambda c: solution[f"pos_{c}"])
    for c in ordered:
        s = solution[f"S_{c}"]
        e = s + duration[c] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": c
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()