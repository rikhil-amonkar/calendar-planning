from z3 import Int, Solver
import json

def main():
    # Create the SMT solver
    s = Solver()

    # Define integer variables for start and end days for each city segment
    B_start = Int("B_start")   # Bucharest start day
    B_end = Int("B_end")       # Bucharest end day
    L_start = Int("L_start")   # Lyon start day
    L_end = Int("L_end")       # Lyon end day
    P_start = Int("P_start")   # Porto start day
    P_end = Int("P_end")       # Porto end day
    wedding_day = Int("wedding_day")  # Wedding day in Bucharest

    # Total trip duration is fixed to 16 days.
    # We will use the structure: Bucharest -> Lyon -> Porto.
    # The overlapping flight days make the count work:
    # Total counted days = (7 + 7 + 4) but two days are overlapped in transitions.
    # Thus calendar days = 18 - 2 = 16.
    
    # Fix trip start and end days.
    s.add(B_start == 1)    # Trip starts on day 1.
    s.add(P_end == 16)     # Trip ends on day 16.
    
    # Duration constraints (each duration includes both endpoints).
    s.add(B_end - B_start + 1 == 7)   # 7 days in Bucharest
    s.add(L_end - L_start + 1 == 7)     # 7 days in Lyon
    s.add(P_end - P_start + 1 == 4)     # 4 days in Porto

    # Flight constraints:
    # If you fly from A to B on day X then that day is counted in both A and B.
    # So we assume the flight happens on the last day of the current city segment.
    s.add(L_start == B_end)   # Flight from Bucharest to Lyon occurs on day B_end.
    s.add(P_start == L_end)   # Flight from Lyon to Porto occurs on day L_end.

    # Wedding constraint: Wedding takes place in Bucharest between day 1 and day 7.
    # Ensure at least one day of the Bucharest stay falls in this window.
    s.add(wedding_day >= 1, wedding_day <= 7)
    s.add(wedding_day >= B_start, wedding_day <= B_end)

    # Check satisfiability and extract the model.
    if s.check().r == 1:
        m = s.model()
        itinerary = [
            {
                "day_range": f"Day {m[B_start]}-{m[B_end]}",
                "place": "Bucharest"
            },
            {
                "day_range": f"Day {m[L_start]}-{m[L_end]}",
                "place": "Lyon"
            },
            {
                "day_range": f"Day {m[P_start]}-{m[P_end]}",
                "place": "Porto"
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no solution is found, return an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()