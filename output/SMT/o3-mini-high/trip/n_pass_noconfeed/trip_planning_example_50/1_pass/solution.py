from z3 import *
import json

def main():
    total_days = 12
    # Define flight day variables:
    # d1: day of flight from Vilnius to Munich
    # d2: day of flight from Munich to Mykonos
    d1 = Int('d1')
    d2 = Int('d2')
    
    s = Solver()
    
    # Flight days must be within the trip duration and in order.
    s.add(d1 >= 1, d1 <= total_days)
    s.add(d2 >= 1, d2 <= total_days)
    s.add(d1 < d2)
    
    # Constraint 1: You want to spend 4 days in Vilnius.
    # If you fly from Vilnius on day d1, you're in Vilnius from Day 1 to d1.
    s.add(d1 == 4)
    
    # Constraint 2: You plan to stay in Munich for 3 days.
    # You arrive in Munich on day d1 (flight day counts for both cities)
    # and depart on day d2, so days in Munich = (d2 - d1 + 1)
    s.add(d2 - d1 + 1 == 3)
    
    # Constraint 3: You would like to visit Mykonos for 7 days.
    # You are in Mykonos from day d2 (flight day counts) until total_days.
    s.add(total_days - d2 + 1 == 7)
    
    if s.check() == sat:
        m = s.model()
        flight_day1 = m[d1].as_long()
        flight_day2 = m[d2].as_long()
        
        # Build itinerary segments.
        # Note: if you fly on day X, you count as being in both departure and arrival cities on day X.
        itinerary = [
            {"day_range": f"Day 1-{flight_day1}", "place": "Vilnius"},
            {"day_range": f"Day {flight_day1}-{flight_day2}", "place": "Munich"},
            {"day_range": f"Day {flight_day2}-{total_days}", "place": "Mykonos"}
        ]
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()