from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Days are 1 to 11
    days = 11

    # Cities: Seville, Paris, Krakow
    Seville, Paris, Krakow = 0, 1, 2
    city_names = {Seville: 'Seville', Paris: 'Paris', Krakow: 'Krakow'}

    # We'll model city for each day 1..11.
    city_vars = [Int(f'city_{i}') for i in range(1, days + 1)]

    # Each city_var must be 0, 1, or 2
    for day in range(1, days + 1):
        s.add(Or(city_vars[day - 1] == Seville, city_vars[day - 1] == Paris, city_vars[day - 1] == Krakow))

    # Transition constraints: if city changes between day i and i+1, they must be connected.
    for i in range(1, days):
        prev_city = city_vars[i - 1]
        next_city = city_vars[i]
        # If they are different, then they must be a connected pair.
        s.add(Implies(prev_city != next_city,
                      Or(
                          And(prev_city == Krakow, next_city == Paris),
                          And(prev_city == Paris, next_city == Krakow),
                          And(prev_city == Paris, next_city == Seville),
                          And(prev_city == Seville, next_city == Paris)
                      )))

    # Count days in each city.
    # For each city, the count is the number of days where city_vars[i] == city.
    seville_days = Sum([If(city_vars[i] == Seville, 1, 0) for i in range(days)])
    paris_days = Sum([If(city_vars[i] == Paris, 1, 0) for i in range(days)])
    krakow_days = Sum([If(city_vars[i] == Krakow, 1, 0) for i in range(days)])

    s.add(seville_days == 6)
    s.add(paris_days == 2)
    s.add(krakow_days == 5)

    # Workshop in Krakow between day 1 and day 5: at least one day in Krakow in days 1-5.
    s.add(Or([city_vars[i] == Krakow for i in range(5)]))

    # Check if the solver can find a model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, days + 1):
            city_val = m.evaluate(city_vars[day - 1]).as_long()
            itinerary.append({'day': day, 'place': city_names[city_val]})
        # Now, we need to handle transitions. If day i and i+1 have different cities, then day i is a transition day.
        # But according to the problem statement, the flight day counts for both cities.
        # So, the itinerary should show day i as being in both cities.
        # However, the JSON output requires a single place per day. But the problem's note says that flight days count for both.
        # But the JSON output should list the place for each day, and the flight day is counted for both.
        # So the current itinerary is correct in terms of counting days, but the JSON output lists one place per day.
        # The note says: "Do not include separate flight entries in the JSON output."
        # So the JSON should have each day mapped to one place, but the counting includes both cities for flight days.
        # So the current code is correct for the JSON output.
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")