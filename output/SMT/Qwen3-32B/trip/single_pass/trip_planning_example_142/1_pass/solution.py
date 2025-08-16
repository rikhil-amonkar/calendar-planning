from z3 import *
import json

def main():
    solver = Solver()

    # Create variables for each day (0: Madrid, 1: Dublin, 2: Tallinn)
    days = [Int(f'day_{i}') for i in range(7)]

    # Each day must be one of the three cities
    for d in days:
        solver.add(Or(d == 0, d == 1, d == 2))

    # Add transition constraints between consecutive days
    for i in range(6):
        prev = days[i]
        curr = days[i + 1]
        allowed = Or(
            prev == curr,
            And(prev == 0, curr == 1),
            And(prev == 1, curr == 0),
            And(prev == 1, curr == 2),
            And(prev == 2, curr == 1)
        )
        solver.add(allowed)

    # Constraints for the workshop in Tallinn on day 6 and 7 (indices 5 and 6)
    solver.add(days[5] == 2)
    solver.add(days[6] == 2)

    # Function to calculate total days in a city based on the contribution rules
    def calculate_total(city_code):
        total = If(days[0] == city_code, 1, 0)
        for i in range(1, 7):
            prev = days[i - 1]
            curr = days[i]
            flight = prev != curr
            contribution = If(
                flight,
                If(prev == city_code, 1, 0) + If(curr == city_code, 1, 0),
                If(curr == city_code, 1, 0)
            )
            total += contribution
        return total

    # Add constraints for the required number of days in each city
    solver.add(calculate_total(0) == 4)  # Madrid
    solver.add(calculate_total(1) == 3)  # Dublin
    solver.add(calculate_total(2) == 2)  # Tallinn

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        # Extract the day assignments
        result = [model.eval(days[i]).as_long() for i in range(7)]
        # Map city codes to names
        cities = {0: "Madrid", 1: "Dublin", 2: "Tallinn"}
        itinerary = [{"day": i + 1, "place": cities[result[i]]} for i in range(7)]
        # Format the output as JSON
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()