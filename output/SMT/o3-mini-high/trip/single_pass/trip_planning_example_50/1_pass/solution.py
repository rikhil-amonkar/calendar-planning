from z3 import *
import json

def main():
    # Total trip days
    total_days = 12

    # Create two integer variables:
    #   d1: the flight day from Vilnius to Munich 
    #   d2: the flight day from Munich to Mykonos
    d1, d2 = Ints('d1 d2')

    s = Solver()

    # The flight days must be within the trip
    s.add(d1 >= 1, d1 <= total_days)
    s.add(d2 >= 1, d2 <= total_days)
    s.add(d1 < d2)  # Flight from Vilnius to Munich must occur before flying to Mykonos

    # Constraint: You want to spend 4 days in Vilnius.
    # If you fly from Vilnius on day d1, then you are in Vilnius on days 1..d1.
    # Thus, d1 must equal 4.
    s.add(d1 == 4)

    # Constraint: You plan to stay in Munich for 3 days.
    # You arrive in Munich on day d1 (flight day counts for both cities) and,
    # if you fly out on day d2, you are in Munich on days d1..d2.
    # Hence the number of Munich days is: d2 - d1 + 1 = 3.
    s.add(d2 - d1 + 1 == 3)

    # Constraint: You would like to visit Mykonos for 7 days.
    # You arrive in Mykonos on day d2 (flight day counts) and remain until day total_days.
    # So the Mykonos stay is: total_days - d2 + 1 = 7.
    s.add(total_days - d2 + 1 == 7)

    if s.check() == sat:
        m = s.model()
        flight_day_vilnius_to_munich = m[d1].as_long()  # Expected to be 4
        flight_day_munich_to_mykonos = m[d2].as_long()    # Expected to be 6
    else:
        print("No solution found")
        return

    # Build itinerary:
    # Note: On a flight day, the day counts for both the originating and arriving cities.
    itinerary = []
    for day in range(1, total_days + 1):
        day_entry = {"day": day}
        if day < flight_day_vilnius_to_munich:
            # Before the first flight, only in Vilnius.
            day_entry["city"] = "Vilnius"
        elif day == flight_day_vilnius_to_munich:
            # On day 4, flying from Vilnius to Munich: count as both.
            day_entry["city"] = ["Vilnius", "Munich"]
        elif flight_day_vilnius_to_munich < day < flight_day_munich_to_mykonos:
            # After arriving in Munich and before the next flight, in Munich.
            day_entry["city"] = "Munich"
        elif day == flight_day_munich_to_mykonos:
            # On day 6, flying from Munich to Mykonos: count as both.
            day_entry["city"] = ["Munich", "Mykonos"]
        else:
            # After day 6, in Mykonos.
            day_entry["city"] = "Mykonos"
        itinerary.append(day_entry)

    # Prepare JSON output.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()