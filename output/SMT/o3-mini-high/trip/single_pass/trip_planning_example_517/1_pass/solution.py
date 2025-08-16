from z3 import *
import json

def main():
    num_days = 19
    # We'll assign integer codes for cities as follows:
    # 0: Dubrovnik
    # 1: Warsaw
    # 2: Stuttgart
    # 3: Bucharest
    # 4: Copenhagen
    cities = ["Dubrovnik", "Warsaw", "Stuttgart", "Bucharest", "Copenhagen"]

    # Required total “stay‐days” (remember: a flight day is counted for both departure and arrival)
    required_days = {
        0: 5,  # Dubrovnik: 5 days
        1: 2,  # Warsaw: 2 days
        2: 7,  # Stuttgart: 7 days
        3: 6,  # Bucharest: 6 days
        4: 3   # Copenhagen: 3 days
    }
    #
    # Note: Because we only have 19 calendar days, and every flight (city change) adds an extra count
    # for the city you leave, the extra total “days” from overlaps is exactly (#flights).
    # Since sum(required_days)=23 and 23-19 = 4, we must have exactly 4 flight days.
    #

    s = Solver()

    # Create one integer variable per day representing the city you are “in” (the day’s primary city).
    itinerary = [Int(f"day_{i}") for i in range(num_days)]
    for d in itinerary:
        s.add(And(d >= 0, d < 5))   # domain is {0,...,4}

    # Allowed direct flight pairs (bidirectional):
    # Warsaw <-> Copenhagen, Stuttgart <-> Copenhagen, Warsaw <-> Stuttgart,
    # Bucharest <-> Copenhagen, Bucharest <-> Warsaw, Copenhagen <-> Dubrovnik.
    def allowed(a, b):
        return Or(
            And(a == 1, b == 4), And(a == 4, b == 1),  # Warsaw <-> Copenhagen
            And(a == 2, b == 4), And(a == 4, b == 2),  # Stuttgart <-> Copenhagen
            And(a == 1, b == 2), And(a == 2, b == 1),  # Warsaw <-> Stuttgart
            And(a == 3, b == 4), And(a == 4, b == 3),  # Bucharest <-> Copenhagen
            And(a == 3, b == 1), And(a == 1, b == 3),  # Bucharest <-> Warsaw
            And(a == 4, b == 0), And(a == 0, b == 4)   # Copenhagen <-> Dubrovnik
        )

    # In our model a change of city from one day to the next means a flight was taken that day.
    # When you fly from city A to city B on day i (i≥1) then day i is counted for B (by its assignment)
    # and also for A (by the flight overlap). Therefore, we add constraints so that if
    # itinerary[i] != itinerary[i-1] then (it must be a direct flight).
    for i in range(1, num_days):
        s.add(If(itinerary[i] != itinerary[i-1], allowed(itinerary[i-1], itinerary[i]), True))

    # Exactly 4 transitions (i.e. flight days) must occur over days 2..19.
    s.add(Sum([If(itinerary[i] != itinerary[i-1], 1, 0) for i in range(1, num_days)]) == 4)

    # Count the total number of days “spent” in each city.
    # Each day i contributes 1 to the city itinerary[i].
    # Additionally, if a flight happens on day i (i>=1) then it also adds 1 to the previous day’s city.
    for city_idx in range(5):
        day_count = Sum([If(itinerary[i] == city_idx, 1, 0) for i in range(num_days)])
        flight_bonus = Sum([If(And(itinerary[i] != itinerary[i-1], itinerary[i-1] == city_idx), 1, 0)
                            for i in range(1, num_days)])
        s.add(day_count + flight_bonus == required_days[city_idx])

    # Conference constraints: On day 7 and day 13 you must be in Stuttgart.
    # Because if you are flying on that day you are considered to be in both the departure and arrival cities,
    # we require that for day 7 (index 6) either the day’s city is Stuttgart or (if a flight occurs)
    # the previous day’s city is Stuttgart.
    s.add(Or(itinerary[6] == 2, And(itinerary[6] != itinerary[5], itinerary[5] == 2)))
    s.add(Or(itinerary[12] == 2, And(itinerary[12] != itinerary[11], itinerary[11] == 2)))

    # Wedding constraint: You must be in Bucharest (3) on at least one day between day 1 and day 6.
    # (On a flight day the city you left counts as being “visited”.)
    wedding_constraints = []
    for i in range(6):
        if i == 0:
            wedding_constraints.append(itinerary[0] == 3)
        else:
            wedding_constraints.append(Or(itinerary[i] == 3,
                                          And(itinerary[i] != itinerary[i-1], itinerary[i-1] == 3)))
    s.add(Or(wedding_constraints))

    # Solve the model.
    if s.check() == sat:
        m = s.model()
        sol = [m[itinerary[i]].as_long() for i in range(num_days)]
        # Build the output itinerary as a list of day-to-city mappings.
        itinerary_list = []
        for i, city_idx in enumerate(sol):
            itinerary_list.append({"day": i+1, "city": cities[city_idx]})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")
        
if __name__ == "__main__":
    main()