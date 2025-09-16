from z3 import *

def main():
    # Define the cities
    City, cities = EnumSort('City', ['Madrid', 'Seville', 'Porto', 'Stuttgart'])
    madrid, seville, porto, stuttgart = cities

    # Required days for each city
    req = {
        madrid: 4,
        seville: 2,
        porto: 3,
        stuttgart: 7
    }

    # Direct flight connections (undirected)
    direct_flights = [
        (porto, stuttgart),
        (seville, porto),
        (madrid, porto),
        (madrid, seville)
    ]

    # Function to check if two cities are connected by a direct flight
    def connected(c1, c2):
        return Or([And(c1 == a, c2 == b) for (a, b) in direct_flights] +
                  [And(c1 == b, c2 == a) for (a, b) in direct_flights])

    # Block assignments for the four segments
    block1 = Const('block1', City)
    block2 = Const('block2', City)
    block3 = Const('block3', City)
    block4 = Const('block4', City)

    # Flight days: f1 (end of block1), f2 (end of block2), f3 (end of block3 and start of block4)
    f1 = Int('f1')
    f2 = Int('f2')
    f3 = Int('f3')

    s = Solver()

    # Block4 must be Stuttgart and cover days 7 to 13 (7 days)
    s.add(block4 == stuttgart)
    s.add(f3 == 7)  # because 14 - f3 = 7 implies f3=7

    # Constraints for stay durations
    s.add(f1 == req[block1])
    s.add(f2 - f1 + 1 == req[block2])
    s.add(8 - f2 == req[block3])  # because 7 - f2 + 1 = 8 - f2

    # Flight days must be in valid range and ordered
    s.add(f1 >= 1, f1 <= 13)
    s.add(f2 > f1, f2 < f3)  # f3 is 7, so f2 < 7
    s.add(f3 == 7)

    # All blocks are distinct
    s.add(Distinct(block1, block2, block3, block4))

    # Consecutive blocks must be connected by direct flights
    s.add(connected(block1, block2))
    s.add(connected(block2, block3))
    s.add(connected(block3, block4))

    # Madrid must be visited between day 1 and 4
    s.add(Or(
        block1 == madrid,
        And(block2 == madrid, f1 <= 4),
        And(block3 == madrid, f2 <= 4)
    ))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Get the block assignments
        block1_val = m[block1]
        block2_val = m[block2]
        block3_val = m[block3]
        block4_val = m[block4]

        # Map Z3 constants to city names
        city_names = {
            madrid: "Madrid",
            seville: "Seville",
            porto: "Porto",
            stuttgart: "Stuttgart"
        }

        block1_name = city_names[block1_val]
        block2_name = city_names[block2_val]
        block3_name = city_names[block3_val]
        block4_name = city_names[block4_val]

        # Get flight days
        f1_val = m[f1].as_long()
        f2_val = m[f2].as_long()
        f3_val = 7  # as per constraint

        # Define blocks: each block is (start_day, end_day, city_name)
        blocks = [
            (1, f1_val, block1_name),
            (f1_val, f2_val, block2_name),
            (f2_val, f3_val, block3_name),
            (f3_val, 13, block4_name)
        ]

        # Build the itinerary
        itinerary = []
        for day in range(1, 14):
            cities_list = []
            for (start, end, city_name) in blocks:
                if day >= start and day <= end:
                    cities_list.append(city_name)
            itinerary.append({"day": day, "city": cities_list})

        # Output as a dictionary with the itinerary
        result = {
            "itinerary": itinerary
        }
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()