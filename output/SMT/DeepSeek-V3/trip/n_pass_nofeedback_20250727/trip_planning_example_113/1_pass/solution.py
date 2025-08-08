from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Cities: Milan, Naples, Seville
    Milan, Naples, Seville = 0, 1, 2
    cities = {Milan: "Milan", Naples: "Naples", Seville: "Seville"}

    # Direct flight connections
    connections = {
        (Milan, Seville),
        (Seville, Milan),
        (Naples, Milan),
        (Milan, Naples)
    }

    # Variables for each day's location (days 1 to 12)
    day_location = [Int(f"day_{i}_loc") for i in range(1, 13)]

    # Constraint: Each day's location must be one of the cities (0, 1, or 2)
    for day in day_location:
        s.add(Or(day == Milan, day == Naples, day == Seville))

    # Constraint: Flight transitions must be direct connections
    for i in range(11):
        current_day = day_location[i]
        next_day = day_location[i + 1]
        s.add(Or(current_day == next_day, (current_day, next_day) in connections))

    # Constraint: Total days in each city
    # Milan: 7 days
    milan_days = Sum([If(day == Milan, 1, 0) for day in day_location])
    s.add(milan_days == 7)

    # Naples: 3 days
    naples_days = Sum([If(day == Naples, 1, 0) for day in day_location])
    s.add(naples_days == 3)

    # Seville: 4 days, with days 9-12 in Seville
    seville_days = Sum([If(day == Seville, 1, 0) for day in day_location])
    s.add(seville_days == 4)
    for i in range(8, 12):  # days 9-12 (0-based index 8-11)
        s.add(day_location[i] == Seville)

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_code = model.evaluate(day_location[i]).as_long()
            city_name = cities[city_code]
            itinerary.append({"day": day_num, "place": city_name})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
print(itinerary)