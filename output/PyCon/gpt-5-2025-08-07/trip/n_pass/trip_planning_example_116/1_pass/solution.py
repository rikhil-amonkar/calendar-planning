import json
from constraint import Problem

def build_and_solve():
    # Inputs
    total_days = 18
    cities = ["London", "Santorini", "Split"]
    desired_days = {"Split": 6, "Santorini": 7, "London": 7}
    conference_requirements = {12: "Santorini", 18: "Santorini"}
    # Allowed direct flights (bidirectional)
    allowed_direct_flights = {
        ("London", "Santorini"), ("Santorini", "London"),
        ("Split", "London"), ("London", "Split")
    }

    # Derived
    required_transitions = sum(desired_days.values()) - total_days  # number of flight days

    # Setup problem
    problem = Problem()
    day_vars = [f"day_{d}" for d in range(1, total_days + 1)]
    problem.addVariables(day_vars, cities)

    # Constraint: allowed transitions (direct flights or stay put)
    def allowed_step(prev, curr):
        return (prev == curr) or ((prev, curr) in allowed_direct_flights)

    for d in range(2, total_days + 1):
        problem.addConstraint(allowed_step, (f"day_{d-1}", f"day_{d}"))

    # Global constraint: city-day counts with flight day double-counting, transitions count,
    # and conference attendance requirements
    def global_constraints(*assignments):
        # Map day -> location
        loc = {d: assignments[d - 1] for d in range(1, total_days + 1)}

        # Count transitions
        transitions = sum(1 for d in range(2, total_days + 1) if loc[d] != loc[d - 1])
        if transitions != required_transitions:
            return False

        # City day counts with double counting on flight days:
        # - Base: every day counts for the current day's location
        # - Extra: if day d (>=2) is a flight day, also count +1 for previous day's city
        counts = {c: 0 for c in cities}
        # Base counts
        for d in range(1, total_days + 1):
            counts[loc[d]] += 1
        # Extra counts for flight days
        for d in range(2, total_days + 1):
            if loc[d] != loc[d - 1]:
                counts[loc[d - 1]] += 1

        # Enforce desired counts
        for c, want in desired_days.items():
            if counts.get(c, 0) != want:
                return False

        # Conference attendance: a day includes a city if:
        # - The day's base location is that city; OR
        # - It's a flight day and the previous day was that city (so day counts for prev city too)
        for day, city in conference_requirements.items():
            in_city = (loc[day] == city) or (day > 1 and loc[day] != loc[day - 1] and loc[day - 1] == city)
            if not in_city:
                return False

        return True

    problem.addConstraint(global_constraints, day_vars)

    solutions = problem.getSolutions()

    if not solutions:
        return {"itinerary": []}

    # Choose an "optimal" solution: minimal transitions (already fixed), tie-breaker lexicographically by locations
    def solution_key(sol):
        loc_list = [sol[f"day_{d}"] for d in range(1, total_days + 1)]
        # transitions count (should be equal across all valid sols)
        t = sum(1 for d in range(2, total_days + 1) if loc_list[d - 1] != loc_list[d - 2])
        return (t, loc_list)

    best = min(solutions, key=solution_key)

    # Build itinerary as contiguous day ranges of base locations
    itinerary = []
    start_day = 1
    current_city = best["day_1"]

    for d in range(2, total_days + 1):
        city = best[f"day_{d}"]
        if city != current_city:
            # Close previous segment at day d-1
            itinerary.append({
                "day_range": f"Day {start_day}-{d-1}",
                "place": current_city
            })
            start_day = d
            current_city = city

    # Close final segment
    itinerary.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": current_city
    })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = build_and_solve()
    print(json.dumps(result))