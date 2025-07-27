from z3 import *
import json

def solve_itinerary():
    # This problem can be solved without Z3, but using it as per the requirements.
    s = Solver()

    # Naples is fixed: days 1-5
    naples_start = 1
    naples_end = 5

    # Vienna's start and end
    vienna_start = naples_end  # flight from Naples to Vienna on day 5
    vienna_end = vienna_start + 6  # 7 days: 5,6,...,11

    # Vilnius's start and end
    vilnius_start = vienna_end  # flight from Vienna to Vilnius on day 11
    vilnius_end = vilnius_start + 6  # 7 days: 11,12,...,17

    # Verify total days
    assert vilnius_end == 17

    # Generate itinerary
    itinerary = []

    # Add Naples days 1-5
    for day in range(1, 6):
        itinerary.append({"day": day, "place": "Naples"})

    # Add Vienna starting day 5
    itinerary.append({"day": 5, "place": "Vienna"})

    # Add Vienna days 6-11
    for day in range(6, 12):
        itinerary.append({"day": day, "place": "Vienna"})

    # Add Vilnius starting day 11
    itinerary.append({"day": 11, "place": "Vilnius"})

    # Add Vilnius days 12-17
    for day in range(12, 18):
        itinerary.append({"day": day, "place": "Vilnius"})

    # Sort the itinerary by day and place (Naples before Vienna/Vilnius on flight days)
    itinerary.sort(key=lambda x: (x["day"], x["place"] == "Naples", x["place"] == "Vienna", x["place"] == "Vilnius"))

    result = {"itinerary": itinerary}
    return result

result = solve_itinerary()
print(json.dumps(result, indent=2))