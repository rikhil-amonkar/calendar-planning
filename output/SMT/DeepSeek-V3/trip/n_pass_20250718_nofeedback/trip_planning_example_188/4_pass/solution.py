from z3 import *

def solve_itinerary():
    # Cities mapping
    BRUSSELS = 1
    BARCELONA = 2
    SPLIT = 3

    # Initialize Z3 solver
    s = Solver()

    # Create variables for each day (1..12)
    days = [Int(f"day_{i}") for i in range(1, 13)]

    # Each day must be one of the cities
    for day in days:
        s.add(Or(day == BRUSSELS, day == BARCELONA, day == SPLIT))

    # Constraint: Days 1 and 2 must be Brussels (conference)
    s.add(days[0] == BRUSSELS)
    s.add(days[1] == BRUSSELS)

    # Flight transitions: only allowed between connected cities
    for i in range(len(days) - 1):
        current = days[i]
        next_day = days[i + 1]
        # Possible transitions:
        # Brussels <-> Barcelona
        # Barcelona <-> Split
        s.add(
            Or(
                current == next_day,  # stay in the same city
                And(current == BRUSSELS, next_day == BARCELONA),
                And(current == BARCELONA, next_day == BRUSSELS),
                And(current == BARCELONA, next_day == SPLIT),
                And(current == SPLIT, next_day == BARCELONA),
            )
        )

    # Function to count days in a city, accounting for flight days
    def count_days(city):
        total = 0
        for i in range(len(days)):
            # Count the day if it's in the city or if it's a flight day involving the city
            condition = Or(
                days[i] == city,
                And(i > 0, days[i] != days[i - 1], Or(days[i] == city, days[i - 1] == city))
            )
            total += If(condition, 1, 0)
        return total

    # Total days constraints
    total_brussels = count_days(BRUSSELS)
    total_barcelona = count_days(BARCELONA)
    total_split = count_days(SPLIT)

    s.add(total_brussels == 2)
    s.add(total_barcelona == 7)
    s.add(total_split == 5)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {BRUSSELS: "Brussels", BARCELONA: "Barcelona", SPLIT: "Split"}
        for i in range(1, 13):
            day_var = days[i - 1]
            city_num = model[day_var].as_long()
            itinerary.append({"day": i, "place": city_names[city_num]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))