from z3 import *

def main():
    # Define the integer variables for the transition days and city assignments
    a = Int('a')  # Last day of the first city segment (flight day to the second city)
    b = Int('b')  # Last day of the second city segment (flight day to the third city)
    c0 = Int('c0')  # First city
    c1 = Int('c1')  # Second city
    c2 = Int('c2')  # Third city

    s = Solver()

    # Define the city mapping: 0: Krakow, 1: Paris, 2: Seville
    # Constraints for the cities: they must be distinct and in {0,1,2}
    s.add(Distinct(c0, c1, c2))
    s.add(c0 >= 0, c0 <= 2)
    s.add(c1 >= 0, c1 <= 2)
    s.add(c2 >= 0, c2 <= 2)

    # Flight connectivity constraints: direct flights between consecutive cities
    # For (c0, c1): must be either (0,1), (1,0), (1,2), (2,1)
    flight1 = Or(
        And(c0 == 0, c1 == 1),
        And(c0 == 1, c1 == 0),
        And(c0 == 1, c1 == 2),
        And(c0 == 2, c1 == 1)
    )
    s.add(flight1)

    # For (c1, c2): similarly
    flight2 = Or(
        And(c1 == 0, c2 == 1),
        And(c1 == 1, c2 == 0),
        And(c1 == 1, c2 == 2),
        And(c1 == 2, c2 == 1)
    )
    s.add(flight2)

    # Days in each city
    days_c0 = a
    days_c1 = b - a + 1
    days_c2 = 12 - b  # Because from day b to day 11 inclusive: 11 - b + 1 = 12 - b

    # Total days per city must match the requirements
    krakow_days = If(c0 == 0, days_c0, If(c1 == 0, days_c1, If(c2 == 0, days_c2, 0)))
    paris_days = If(c0 == 1, days_c0, If(c1 == 1, days_c1, If(c2 == 1, days_c2, 0)))
    seville_days = If(c0 == 2, days_c0, If(c1 == 2, days_c1, If(c2 == 2, days_c2, 0)))

    s.add(krakow_days == 5)
    s.add(paris_days == 2)
    s.add(seville_days == 6)

    # Workshop constraint: must be in Krakow on at least one day between 1 and 5
    s.add(Or(
        c0 == 0,  # Krakow is the first city: we are there from day1 to day a (and a>=1, so day1 is in [1,5])
        And(c1 == 0, a <= 5),  # Krakow is the second city: we are there from day a to day b, so we require a<=5 to have at least one day in [1,5]
        And(c2 == 0, b <= 5)   # Krakow is the third city: we are there from day b to day11, so we require b<=5 to have at least one day in [1,5]
    ))

    # Constraints on a and b
    s.add(a >= 1, a <= 11)
    s.add(b >= a, b <= 11)

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        a_val = model[a].as_long()
        b_val = model[b].as_long()
        c0_val = model[c0].as_long()
        c1_val = model[c1].as_long()
        c2_val = model[c2].as_long()

        city_map = {0: "Krakow", 1: "Paris", 2: "Seville"}
        c0_name = city_map[c0_val]
        c1_name = city_map[c1_val]
        c2_name = city_map[c2_val]

        # Build the itinerary
        itinerary = [
            {"day_range": f"Day 1-{a_val}", "place": c0_name},
            {"day_range": f"Day {a_val}", "place": c0_name},
            {"day_range": f"Day {a_val}", "place": c1_name},
            {"day_range": f"Day {a_val}-{b_val}", "place": c1_name},
            {"day_range": f"Day {b_val}", "place": c1_name},
            {"day_range": f"Day {b_val}", "place": c2_name},
            {"day_range": f"Day {b_val}-11", "place": c2_name}
        ]

        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()