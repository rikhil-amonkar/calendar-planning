import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables and constraints
    total_days = 18
    cities = [
        "Barcelona",
        "Frankfurt",
        "Florence",
        "Stockholm",
        "Salzburg",
        "Stuttgart",
        "Venice",
    ]

    # Desired durations in each city (in days), counting overlap on flight days
    desired_days = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3,
    }

    # Allowed direct flights (undirected)
    direct_pairs = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt"),
    ]
    direct_edges = {frozenset((a, b)) for a, b in direct_pairs}

    # Verify total calendar days = sum(desired_days) - number_of_flights
    # Number of flights = segments - 1 = number of cities - 1
    num_flights = len(cities) - 1
    if sum(desired_days.values()) - num_flights != total_days:
        raise ValueError("Inconsistent total days with desired durations and flights.")

    # Constraint model: sequence of 7 segments (positions) visiting each city once
    problem = Problem()

    positions = [f"P{i}" for i in range(1, len(cities) + 1)]
    for p in positions:
        problem.addVariable(p, cities)

    # All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), positions)

    # Start in Venice to attend show Day 1-5
    problem.addConstraint(lambda c: c == "Venice", ("P1",))

    # Salzburg must be endpoint (degree 1 city) and Venice is already at start, so place Salzburg at end
    problem.addConstraint(lambda c: c == "Salzburg", (positions[-1],))

    # Consecutive positions must be directly connected by a flight
    for i in range(1, len(positions)):
        prev_pos = f"P{i}"
        curr_pos = f"P{i+1}"
        problem.addConstraint(lambda a, b, E=direct_edges: frozenset((a, b)) in E, (prev_pos, curr_pos))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        print(json.dumps({"itinerary": [], "error": "No feasible itinerary found"}))
        return

    # Choose a deterministic solution (lexicographically minimal sequence)
    def seq_tuple(sol):
        return tuple(sol[f"P{i}"] for i in range(1, len(cities) + 1))

    best_solution = min(solutions, key=seq_tuple)
    ordered_cities = [best_solution[f"P{i}"] for i in range(1, len(cities) + 1)]

    # Build itinerary with overlapping flight days:
    # If flight from A to B happens on day X, both A and B include day X.
    itinerary = []
    current_start = 1
    for city in ordered_cities:
        d = desired_days[city]
        current_end = current_start + d - 1
        itinerary.append({
            "day_range": f"Day {current_start}-{current_end}",
            "place": city
        })
        # Overlap next segment start with current end to model flight day counting in both cities
        current_start = current_end

    # Validate final day equals total_days
    final_end_day = int(itinerary[-1]["day_range"].split("-")[1])
    assert final_end_day == total_days, f"Final end day {final_end_day} != {total_days}"

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()