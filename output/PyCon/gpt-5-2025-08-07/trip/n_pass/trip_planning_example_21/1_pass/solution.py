import json
from constraint import Problem
from itertools import permutations

def main():
    # Input variables (can be adjusted)
    total_days = 10
    cities = ["Mykonos", "Vienna", "Venice"]
    required_days = {
        "Venice": 6,
        "Mykonos": 2,
        "Vienna": 4,
    }
    # Direct flight connections (bidirectional)
    direct_flights = {("Mykonos", "Vienna"), ("Vienna", "Venice")}
    direct_flights |= {(b, a) for (a, b) in list(direct_flights)}
    # Workshop window (inclusive)
    workshop_start, workshop_end = 5, 10

    # Generate all valid city visit orders that use only direct flights
    def valid_orders():
        for order in permutations(cities, 3):
            if (order[0], order[1]) in direct_flights and (order[1], order[2]) in direct_flights:
                yield order
    allowed_orders = list(valid_orders())

    # Set up CSP
    problem = Problem()
    problem.addVariable("order", allowed_orders)
    problem.addVariable("t1", range(1, total_days + 1))   # travel day from order[0] -> order[1]
    problem.addVariable("t2", range(1, total_days + 1))   # travel day from order[1] -> order[2]
    problem.addVariable("workshop_day", range(workshop_start, workshop_end + 1))

    # Helper to compute totals given an assignment
    def compute_totals(order, t1, t2):
        # Base city of each day (without overlap credit for arrival city on travel days)
        if not (1 <= t1 < t2 <= total_days):
            return None
        base0 = t1
        base1 = t2 - t1
        base2 = total_days - t2
        totals = {
            order[0]: base0,               # departure city counts the travel day (already in base)
            order[1]: base1 + 1,           # arrival city gets +1 for travel day t1
            order[2]: base2 + 1,           # arrival city gets +1 for travel day t2
        }
        return totals

    # Constraint: durations match required city days
    def duration_constraint(order, t1, t2):
        totals = compute_totals(order, t1, t2)
        if totals is None:
            return False
        return all(totals[c] == required_days[c] for c in cities)

    # Constraint: workshop day presence in Venice
    def workshop_presence_constraint(order, t1, t2, workshop_day):
        if not (1 <= t1 < t2 <= total_days):
            return False
        d = workshop_day
        # Determine presence including overlaps:
        # Base presence
        if d <= t1:
            base_city = order[0]
        elif d <= t2:
            base_city = order[1]
        else:
            base_city = order[2]
        present = base_city == "Venice"
        # Add arrival presence on exact travel days
        if d == t1 and order[1] == "Venice":
            present = True
        if d == t2 and order[2] == "Venice":
            present = True
        return present

    problem.addConstraint(duration_constraint, ("order", "t1", "t2"))
    problem.addConstraint(workshop_presence_constraint, ("order", "t1", "t2", "workshop_day"))

    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    # Score solutions to pick an "optimal" one:
    # - Minimize Venice days before workshop window (days < workshop_start)
    # - Then minimize workshop_day (earlier attendance)
    # - Then prefer order ("Mykonos","Vienna","Venice") for a natural eastward flow
    # - Then minimize t1, t2 (earlier transitions)
    def venice_presence_days(order, t1, t2):
        # Presence ranges (including overlaps):
        # order[0]: days 1..t1
        # order[1]: days t1..t2
        # order[2]: days t2..total_days
        if order[0] == "Venice":
            start, end = 1, t1
        elif order[1] == "Venice":
            start, end = t1, t2
        else:  # order[2] == "Venice"
            start, end = t2, total_days
        return set(range(start, end + 1))

    def score(sol):
        order, t1, t2, wd = sol["order"], sol["t1"], sol["t2"], sol["workshop_day"]
        v_days = venice_presence_days(order, t1, t2)
        pre_window_venice = len([d for d in v_days if d < workshop_start])
        order_rank = 0 if order == ("Mykonos", "Vienna", "Venice") else 1
        return (pre_window_venice, wd, order_rank, t1, t2)

    best_sol = min(solutions, key=score)
    order, t1, t2 = best_sol["order"], best_sol["t1"], best_sol["t2"]

    # Construct itinerary as overlapping day ranges reflecting travel-day double counting
    itinerary = [
        {"day_range": f"Day 1-{t1}", "place": order[0]},
        {"day_range": f"Day {t1}-{t2}", "place": order[1]},
        {"day_range": f"Day {t2}-{total_days}", "place": order[2]},
    ]

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()