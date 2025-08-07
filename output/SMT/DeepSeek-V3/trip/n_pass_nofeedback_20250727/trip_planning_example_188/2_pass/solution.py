from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Days are 1 to 12
    days = range(1, 13)
    cities = ['Brussels', 'Barcelona', 'Split']
    city_codes = {city: idx for idx, city in enumerate(cities)}

    # Create variables for each day: which city the traveler is in
    # Each day can be in one or two cities (if it's a flight day)
    # We'll model each day as a list of cities (length 1 or 2)
    # But since Z3 doesn't handle lists directly, we'll use two variables per day:
    # - primary city (must be set)
    # - secondary city (optional, -1 if not set)
    primary = {day: Int(f'primary_{day}') for day in days}
    secondary = {day: Int(f'secondary_{day}') for day in days}

    # City encodings: 0: Brussels, 1: Barcelona, 2: Split, -1: invalid/not used
    for day in days:
        s.add(primary[day] >= 0, primary[day] <= 2)
        s.add(secondary[day] >= -1, secondary[day] <= 2)
        # If secondary is not -1, then it must be a different city from primary
        s.add(If(secondary[day] != -1, primary[day] != secondary[day], True))

    # Flight constraints: secondary city can only be set if there's a direct flight between primary and secondary
    for day in days:
        # Possible flights:
        # Brussels (0) <-> Barcelona (1)
        # Barcelona (1) <-> Split (2)
        s.add(If(secondary[day] != -1,
                 Or(
                     And(primary[day] == 0, secondary[day] == 1),
                     And(primary[day] == 1, secondary[day] == 0),
                     And(primary[day] == 1, secondary[day] == 2),
                     And(primary[day] == 2, secondary[day] == 1)
                 ),
                 True))

    # Constraints for days 1 and 2: must be in Brussels (no flights on these days)
    s.add(primary[1] == 0)
    s.add(secondary[1] == -1)
    s.add(primary[2] == 0)
    s.add(secondary[2] == -1)

    # Continuity constraints: primary of day d+1 must be either primary or secondary of day d
    for d in range(1, 12):
        s.add(Or(
            primary[d+1] == primary[d],
            And(secondary[d] != -1, primary[d+1] == secondary[d])
        ))

    # Count days in each city
    brussels_days = Int('brussels_days')
    barcelona_days = Int('barcelona_days')
    split_days = Int('split_days')

    # Initialize counts
    s.add(brussels_days == Sum([If(Or(primary[day] == 0, secondary[day] == 0), 1, 0) for day in days]))
    s.add(barcelona_days == Sum([If(Or(primary[day] == 1, secondary[day] == 1), 1, 0) for day in days]))
    s.add(split_days == Sum([If(Or(primary[day] == 2, secondary[day] == 2), 1, 0) for day in days]))

    # Add required days
    s.add(brussels_days == 2)
    s.add(barcelona_days == 7)
    s.add(split_days == 5)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []

        for day in days:
            primary_city = m.evaluate(primary[day]).as_long()
            secondary_city_val = m.evaluate(secondary[day])
            if secondary_city_val.as_long() != -1:
                secondary_city = secondary_city_val.as_long()
                cities_on_day = [cities[primary_city], cities[secondary_city]]
                # Sort to make the output consistent (optional)
                cities_on_day.sort()
                itinerary.append({"day": day, "cities": cities_on_day})
            else:
                itinerary.append({"day": day, "cities": [cities[primary_city]]})

        # Convert to the required JSON format
        result = {
            "itinerary": itinerary
        }
        return result
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))