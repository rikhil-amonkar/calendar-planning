import json
from z3 import *

def main():
    # Create Z3 integer variables for flight days and workshop day.
    # flight1: day of flight from Madrid to Dublin
    # flight2: day of flight from Dublin to Tallinn
    flight1 = Int('flight1')
    flight2 = Int('flight2')
    workshop_day = Int('workshop_day')

    s = Solver()

    # Define the domain of flight days: They must fall within the 7-day trip.
    s.add(flight1 >= 1, flight1 <= 7)
    s.add(flight2 >= 1, flight2 <= 7)
    s.add(flight1 < flight2)  # Must take the Madrid->Dublin flight before Dublin->Tallinn.

    # Constraints for days spent in each city.
    # If you fly from A to B on day X, that day counts for both A and B.

    # Madrid: days 1 to flight1 (inclusive). Total days in Madrid = flight1.
    # We require exactly 4 days in Madrid.
    s.add(flight1 == 4)

    # Dublin: days flight1 to flight2 (inclusive). Total days = flight2 - flight1 + 1.
    # We require exactly 3 days in Dublin.
    s.add(flight2 - flight1 + 1 == 3)

    # Tallinn: days flight2 to day 7 (inclusive). Total days = 7 - flight2 + 1 = 8 - flight2.
    # We require exactly 2 days in Tallinn.
    s.add(8 - flight2 == 2)

    # Workshop constraint in Tallinn:
    # The workshop must be attended on either day 6 or day 7, and the participant must already be
    # in Tallinn. Since Tallinn starts on flight2 and runs until day 7, we require:
    s.add(Or(workshop_day == 6, workshop_day == 7))
    s.add(workshop_day >= flight2, workshop_day <= 7)

    # Flight connectivity constraints:
    # Direct flights exist between Madrid and Dublin, and between Dublin and Tallinn.
    # Our ordering (Madrid -> Dublin -> Tallinn) is valid if flight1 and flight2 occur on the appropriate days.
    
    if s.check() == sat:
        m = s.model()
        # Retrieve the computed flight days.
        f1 = m[flight1].as_long()  # Expected to be 4.
        f2 = m[flight2].as_long()  # Expected to be 6.
        w_day = m[workshop_day].as_long()  # Either 6 or 7.

        # Build the itinerary:
        # Note: The flight days are double counted (e.g., day 4 is in both Madrid and Dublin).
        itinerary = [
            {"day_range": f"Day 1-{f1}", "place": "Madrid"},
            {"day_range": f"Day {f1}-{f2}", "place": "Dublin"},
            {"day_range": f"Day {f2}-7", "place": "Tallinn"}
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no plan is found (should not happen with the given constraints).
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()