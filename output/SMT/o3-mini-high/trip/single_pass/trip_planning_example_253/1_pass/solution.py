from z3 import *

def main():
    solver = Solver()
    n = 14  # 14 days, indexed 0..13 representing Days 1..14

    # We use an integer coding for cities:
    # 0: Amsterdam, 1: Vienna, 2: Santorini, 3: Lyon
    city_names = {0: "Amsterdam", 1: "Vienna", 2: "Santorini", 3: "Lyon"}

    # Create an array of variables, one per day.
    days = [Int("day_%d" % (i+1)) for i in range(n)]
    for d in days:
        solver.add(And(d >= 0, d <= 3))

    # Define allowed direct flights between cities.
    # Allowed pairs (a,b) meaning a flight from a to b or b to a is allowed:
    #   Vienna <-> Lyon, Vienna <-> Santorini, Vienna <-> Amsterdam,
    #   Amsterdam <-> Santorini, and Lyon <-> Amsterdam.
    def allowed(a, b):
        return Or(
            And(a == 1, b == 3), And(a == 3, b == 1),  # Vienna and Lyon
            And(a == 1, b == 2), And(a == 2, b == 1),  # Vienna and Santorini
            And(a == 1, b == 0), And(a == 0, b == 1),  # Vienna and Amsterdam
            And(a == 0, b == 2), And(a == 2, b == 0),  # Amsterdam and Santorini
            And(a == 3, b == 0), And(a == 0, b == 3)   # Lyon and Amsterdam
        )

    # For each day (except the first) we want to know if a flight is taken.
    # IMPORTANT: If days[i] != days[i-1] then day i is a flight day,
    # meaning that day counts for both cities: the departure (day i-1) and arrival (day i).
    flight_transitions = []
    for i in range(1, n):
        # Define an indicator: 1 if a flight occurred on this day.
        flight = If(days[i] != days[i-1], 1, 0)
        flight_transitions.append(flight)
        # When a flight occurs, it must be along an allowed direct connection.
        # Otherwise the city stays the same.
        solver.add(Or(days[i] == days[i-1], allowed(days[i-1], days[i])))

    # We know exactly 3 flight days (each flight day gets double‐counted) 
    # so that the overall effective days add up to 14+3 = 17.
    solver.add(Sum(flight_transitions) == 3)

    # Define "effective" days spent in each city.
    # A day always counts for the primary city assignment.
    # Additionally, on any day i (i>=1) with a flight (i.e. if days[i]!=days[i-1]),
    # we add one extra day to the previous city (days[i-1]) because that day is shared.
    counts = {}
    for c in range(4):
        primary = Sum([If(days[i] == c, 1, 0) for i in range(n)])
        extra   = Sum([If(And(i >= 1, days[i] != days[i-1], days[i-1] == c), 1, 0) for i in range(1, n)])
        counts[c] = primary + extra

    # Add the requirements:
    # Amsterdam: 3 days, Vienna: 7 days, Santorini: 4 days, Lyon: 3 days.
    solver.add(counts[0] == 3)  # Amsterdam
    solver.add(counts[1] == 7)  # Vienna
    solver.add(counts[2] == 4)  # Santorini
    solver.add(counts[3] == 3)  # Lyon

    # Additional event constraints:
    #
    # Workshop in Amsterdam between day 9 and day 11
    # (i.e. on one of Days 9, 10, or 11).
    # Because on a flight day the traveler is in both the departure and arrival cities,
    # we require that for some day j in {9,10,11} (indexed as 8,9,10) either:
    #   - the primary city on that day is Amsterdam, OR
    #   - it is a flight day and the previous day’s city is Amsterdam.
    workshop_options = []
    for i in [8, 9, 10]:
        cond = Or(days[i] == 0, And(i >= 1, days[i] != days[i-1], days[i-1] == 0))
        workshop_options.append(cond)
    solver.add(Or(workshop_options))

    # Wedding in Lyon between day 7 and day 9 (i.e. Days 7, 8 or 9; indexed as 6,7,8).
    wedding_options = []
    for i in [6, 7, 8]:
        cond = Or(days[i] == 3, And(i >= 1, days[i] != days[i-1], days[i-1] == 3))
        wedding_options.append(cond)
    solver.add(Or(wedding_options))

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        # Build a list of day-to-city mappings.
        # On every day i, if i>0 and a flight occurs (model value changes),
        # then day i counts as a flight day and we list both the departure city and arrival city.
        sol = [model.evaluate(days[i]) for i in range(n)]
        for i in range(n):
            day_num = i + 1
            if i > 0 and sol[i] != sol[i-1]:
                # Flight day: include both cities.
                cities = [
                    city_names[int(sol[i-1].as_long())],
                    city_names[int(sol[i].as_long())]
                ]
                itinerary.append({"day": day_num, "city": cities})
            else:
                itinerary.append({"day": day_num, "city": city_names[int(sol[i].as_long())]})
        
        # Output as JSON.
        import json
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()