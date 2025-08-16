from z3 import Int, Solver, sat
import json

def main():
    # Define decision variables:
    # flight_Dublin_Riga is the flight day when you fly from Dublin to Riga.
    # flight_Riga_Vilnius is the flight day when you fly from Riga to Vilnius.
    flight_Dublin_Riga = Int('flight_Dublin_Riga')
    flight_Riga_Vilnius = Int('flight_Riga_Vilnius')
    
    s = Solver()
    
    # The whole trip lasts 12 days (days 1 through 12).
    # On a flight day, the day counts for both departure and arrival cities.
    
    # Domain constraints: flight days must be within the trip range and in order.
    s.add(flight_Dublin_Riga >= 1, flight_Dublin_Riga <= 12)
    s.add(flight_Riga_Vilnius >= 1, flight_Riga_Vilnius <= 12)
    s.add(flight_Dublin_Riga < flight_Riga_Vilnius)

    # Itinerary requirements (remember, flight day counts for both cities):
    # • Dublin must be visited for 2 days.
    # • Riga must be visited for 5 days.
    # • Vilnius must be visited for 7 days.
    #
    # We plan the route in order: Start in Dublin → fly to Riga → fly to Vilnius.
    #
    # If we fly from Dublin to Riga on day X, then:
    #   - Dublin is counted for Days 1 through X (X days total).
    # Similarly, if we fly from Riga to Vilnius on day Y, then:
    #   - Riga is counted for Days X through Y (inclusive, Y - X + 1 days).
    #   - Vilnius is counted for Days Y through 12 (inclusive, 13 - Y days).
    
    # Impose the constraints:
    s.add(flight_Dublin_Riga == 2)  # Dublin gets Days 1-2 → 2 days exactly.
    s.add(flight_Riga_Vilnius - flight_Dublin_Riga + 1 == 5)  # Riga gets 5 days.
    s.add(13 - flight_Riga_Vilnius == 7)  # Vilnius gets 7 days.

    if s.check() == sat:
        m = s.model()
        flight1 = m[flight_Dublin_Riga].as_long()
        flight2 = m[flight_Riga_Vilnius].as_long()
        
        itinerary = []
        # Construct the itinerary day by day.
        # On a flight day, we list both the departure and destination cities.
        for day in range(1, 13):
            if day == flight1:
                # Flight from Dublin to Riga: day counts for both.
                day_places = ["Dublin", "Riga"]
            elif day == flight2:
                # Flight from Riga to Vilnius: day counts for both.
                day_places = ["Riga", "Vilnius"]
            elif day < flight1:
                day_places = ["Dublin"]
            elif flight1 < day < flight2:
                day_places = ["Riga"]
            else:  # day > flight2
                day_places = ["Vilnius"]
            itinerary.append({"day": day, "cities": day_places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()