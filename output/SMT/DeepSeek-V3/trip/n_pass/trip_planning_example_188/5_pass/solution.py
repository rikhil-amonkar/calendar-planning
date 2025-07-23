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
    
    # Create flight indicators for each day (True if flight occurs on that day)
    flights = [Bool(f"flight_{i}") for i in range(1, 13)]

    # Each day must be one of the cities
    for day in days:
        s.add(Or(day == BRUSSELS, day == BARCELONA, day == SPLIT))

    # Constraint: Days 1 and 2 must be Brussels (conference)
    s.add(days[0] == BRUSSELS)
    s.add(days[1] == BRUSSELS)
    s.add(Not(flights[0]))  # No flight on day 1
    s.add(Not(flights[1]))  # No flight on day 2

    # Flight constraints
    for i in range(1, len(days)):
        # A flight can only occur if the city changes
        s.add(Implies(flights[i], days[i] != days[i-1]))
        # Only allow direct flights
        s.add(Implies(flights[i], Or(
            And(days[i-1] == BRUSSELS, days[i] == BARCELONA),
            And(days[i-1] == BARCELONA, days[i] == BRUSSELS),
            And(days[i-1] == BARCELONA, days[i] == SPLIT),
            And(days[i-1] == SPLIT, days[i] == BARCELONA)
        )))

    # Function to count days in a city, accounting for flight days
    def count_days(city):
        total = 0
        for i in range(len(days)):
            # Count the day if:
            # 1. It's in the city, or
            # 2. It's a flight day involving the city
            condition = Or(
                days[i] == city,
                And(flights[i], Or(
                    And(i > 0, days[i-1] == city),
                    days[i] == city
                ))
            )
            total += If(condition, 1, 0)
        return total

    # Total days constraints
    s.add(count_days(BRUSSELS) == 2)
    s.add(count_days(BARCELONA) == 7)
    s.add(count_days(SPLIT) == 5)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {BRUSSELS: "Brussels", BARCELONA: "Barcelona", SPLIT: "Split"}
        for i in range(1, 13):
            day_var = days[i-1]
            flight_var = flights[i-1]
            city_num = model[day_var].as_long()
            is_flight = model.eval(flight_var)
            itinerary.append({
                "day": i,
                "place": city_names[city_num],
                "flight": is_flight
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))