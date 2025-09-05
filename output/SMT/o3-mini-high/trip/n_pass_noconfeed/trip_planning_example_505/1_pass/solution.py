from z3 import *
import json

def main():
    s = Solver()

    # Enumerate the cities by an integer representation:
    # 0: Prague, 1: Stuttgart, 2: Split, 3: Krakow, 4: Florence.
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
    # Required durations (in days) staying in each city.
    durations = [4, 2, 2, 2, 2]  # indices correspond to cities list

    n = 5  # number of cities to visit (order length)
    # order[i] will be the integer that identifies which city is visited at position i.
    order = [Int(f"order_{i}") for i in range(n)]
    # S[i] will be the starting day (arrival day) for the city in position i.
    S = [Int(f"S_{i}") for i in range(n)]

    # Domain constraints for order: each must be between 0 and 4.
    for i in range(n):
        s.add(And(order[i] >= 0, order[i] <= 4))
    s.add(Distinct(order))  # All cities must be visited exactly once.

    # Domain constraints for starting days S[i]: they must be within the itinerary days.
    # Our trip runs from day 1 to day 8.
    for i in range(n):
        s.add(And(S[i] >= 1, S[i] <= 8))

    # The itinerary is consecutive. We fix the first day's start.
    s.add(S[0] == 1)

    # Helper function: given a city variable (an Int), return its required duration.
    def duration_for(city_var):
        return If(city_var == 0, durations[0],
               If(city_var == 1, durations[1],
               If(city_var == 2, durations[2],
               If(city_var == 3, durations[3],
               If(city_var == 4, durations[4], 0)))))

    # Consecutive cities share an overlap day (the flight day).
    # For city at position i, its end day is S[i] + duration - 1.
    # And the next city starts on that same day.
    for i in range(n - 1):
        s.add(S[i + 1] == S[i] + duration_for(order[i]) - 1)

    # Total itinerary: last city's end-day should be day 8.
    s.add(S[n - 1] + duration_for(order[n - 1]) - 1 == 8)

    # Special constraint: The wedding in Stuttgart is between Day 2 and Day 3.
    # So if Stuttgart (city 1) is visited, its interval must cover days 2 and 3.
    # Given a 2-day stay, the only possibility is to start on Day 2.
    for i in range(n):
        s.add(Implies(order[i] == 1, S[i] == 2))

    # Special constraint: Meet friends in Split (city 2) between Day 3 and Day 4.
    # For a 2-day stay, the start can be 2, 3, or 4 such that the interval (start, start+1)
    # intersects with the window {3,4}. (If start==2, interval is [2,3]; if start==3, [3,4];
    # if start==4, [4,5]. In all cases, either day 3 or 4 is present.)
    for i in range(n):
        s.add(Implies(order[i] == 2, Or(S[i] == 2, S[i] == 3, S[i] == 4)))

    # Define allowed direct flights between cities.
    # The given direct flights (bidirectional) are:
    # Stuttgart <-> Split, Prague <-> Florence, Krakow <-> Stuttgart,
    # Krakow <-> Split, Split <-> Prague, Krakow <-> Prague.
    allowed_flights = [
        (1, 2), (2, 1),     # Stuttgart and Split
        (0, 4), (4, 0),     # Prague and Florence
        (3, 1), (1, 3),     # Krakow and Stuttgart
        (3, 2), (2, 3),     # Krakow and Split
        (2, 0), (0, 2),     # Split and Prague
        (3, 0), (0, 3)      # Krakow and Prague
    ]

    # For each flight (transition between consecutive cities in our itinerary),
    # enforce that a direct flight is available.
    for i in range(n - 1):
        flightConstraints = []
        for (cityA, cityB) in allowed_flights:
            flightConstraints.append(And(order[i] == cityA, order[i+1] == cityB))
        s.add(Or(flightConstraints))

    # Solve the SMT problem.
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            city_index = m.evaluate(order[i]).as_long()
            start_day = m.evaluate(S[i]).as_long()
            d = durations[city_index]
            end_day = start_day + d - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()