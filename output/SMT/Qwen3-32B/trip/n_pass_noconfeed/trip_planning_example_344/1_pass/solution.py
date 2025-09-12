from z3 import *
import json

def main():
    # Define cities as integers for easier handling
    VAL, ATH, NAP, ZUR = 0, 1, 2, 3

    # Define allowed direct flights between cities as pairs (a, b)
    allowed_flights = [
        (VAL, ATH), (ATH, VAL),
        (VAL, NAP), (NAP, VAL),
        (ATH, NAP), (NAP, ATH),
        (ATH, ZUR), (ZUR, ATH),
        (NAP, ZUR), (ZUR, NAP),
        (ZUR, VAL), (VAL, ZUR),
    ]

    solver = Solver()

    # Create variables for the four segments
    s = [Int(f's{i}') for i in range(4)]  # s[0], s[1], s[2], s[3]

    # Constraints: all cities are distinct and in the valid range
    solver.add(Distinct(s))
    for city in s:
        solver.add(And(city >= 0, city <= 3))

    # Add constraints for allowed transitions between consecutive cities
    for i in range(3):
        current = s[i]
        next_city = s[i+1]
        transitions = []
        for a, b in allowed_flights:
            transitions.append(And(current == a, next_city == b))
        solver.add(Or(transitions))

    # Compute durations for each segment based on city
    durations = []
    for city in s:
        durations.append(If(city == NAP, 5, 6))

    # Compute start days for each segment
    start_days = [1]  # start_day_0 is 1
    start_days.append(durations[0])  # start_day_1 is duration_0
    start_days.append(durations[0] + durations[1] - 1)  # start_day_2
    start_days.append(durations[0] + durations[1] + durations[2] - 2)  # start_day_3

    # Add constraints for Athens and Naples
    for i in range(4):
        solver.add(Implies(s[i] == ATH, start_days[i] <= 6))
        solver.add(Implies(s[i] == NAP, start_days[i] >= 12))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        cities_order = [model.eval(s[i]).as_long() for i in range(4)]
        # Generate itinerary
        itinerary = []
        for i in range(4):
            city = cities_order[i]
            start = model.eval(start_days[i]).as_long()
            duration = 5 if city == NAP else 6
            end = start + duration - 1
            city_name = {0: 'Valencia', 1: 'Athens', 2: 'Naples', 3: 'Zurich'}[city]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})
        # Output JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()