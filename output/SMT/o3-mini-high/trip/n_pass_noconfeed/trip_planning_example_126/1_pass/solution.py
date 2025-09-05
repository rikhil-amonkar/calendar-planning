from z3 import Solver, Int, sat
import json

def main():
    # Total trip days
    T = 11

    # Create SMT solver instance
    s = Solver()

    # Define flight day variables:
    # f1: the day when you fly from the first city to the second.
    # f2: the day when you fly from the second city to the third.
    f1 = Int('f1')
    f2 = Int('f2')

    # Basic constraints: flight days occur within the trip, with f1 < f2.
    s.add(f1 >= 1, f1 < f2, f2 <= T)

    # We consider a fixed city order that respects available direct flights:
    # City 1: Krakow, City 2: Paris, City 3: Seville.
    # (Flights: Krakow<->Paris and Paris<->Seville are available.)
    
    # Duration computation: if you take a flight on day X,
    # you count day X in both the departing and arriving city.
    # Thus, with flight days f1 and f2, the durations are:
    #   Krakow: days 1 to f1  -> duration = f1 days.
    #   Paris: days f1 to f2   -> duration = (f2 - f1 + 1) days.
    #   Seville: days f2 to T  -> duration = (T - f2 + 1) days.

    # Trip constraints:
    # Stay exactly 5 days in Krakow, 2 days in Paris, and 6 days in Seville.
    s.add(f1 == 5)                   # Krakow: f1 must equal 5 days.
    s.add(f2 - f1 + 1 == 2)            # Paris: f2 - 5 + 1 = 2  -> f2 = 6.
    s.add(T - f2 + 1 == 6)             # Seville: 11 - f2 + 1 = 6  -> f2 = 6.

    # Workshop constraint: Attend a workshop in Krakow between Day 1 and Day 5.
    # Since the first city is Krakow and the segment is Day 1 to Day f1, 
    # this condition is automatically met.

    # Check if the constraints are satisfiable.
    if s.check() == sat:
        m = s.model()
        flight1 = m[f1].as_long()
        flight2 = m[f2].as_long()

        # Build the itinerary based on computed flight days.
        itinerary = [
            {"day_range": f"Day 1-{flight1}", "place": "Krakow"},
            {"day_range": f"Day {flight1}-{flight2}", "place": "Paris"},
            {"day_range": f"Day {flight2}-{T}", "place": "Seville"}
        ]

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # No valid itinerary found.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()