from z3 import *
import json

def main():
    s = Solver()
    
    # We use three integer variables for the flight days:
    # x1: flight day from Vilnius to Split (Vilnius segment: days 1 to x1)
    # x2: flight day from Split to Madrid (Split segment: days x1 to x2)
    # x3: flight day from Madrid to Santorini (Madrid segment: days x2 to x3)
    #
    # When flying, the flight day counts for both departing and arriving cities.
    # Hence the duration for a segment from day a to b is (b - a + 1) days.
    
    x1, x2, x3 = Ints('x1 x2 x3')
    
    # Constraint for the required durations:
    # Vilnius: 4 days, so if Vilnius is from day 1 to x1 then:  x1 - 1 + 1 = x1  must equal 4.
    s.add(x1 == 4)
    
    # Split: 5 days, with segment [x1, x2] => (x2 - x1 + 1) = 5.
    s.add(x2 - x1 + 1 == 5)
    
    # Madrid: 6 days, with segment [x2, x3] => (x3 - x2 + 1) = 6.
    s.add(x3 - x2 + 1 == 6)
    
    # Santorini: 2 days, with segment [x3, 14] => (14 - x3 + 1) = 2.
    s.add(14 - x3 + 1 == 2)
    
    # Ensure the ordering and valid day ranges
    s.add(1 <= x1, x1 <= x2, x2 <= x3, x3 <= 14)
    
    # Additional note: We must be in Santorini on days 13 and 14 for the conference.
    # In our plan the Madrid-to-Santorini flight happens on day x3;
    # if x3 is 13, then day 13 (the flight day) and day 14 will include Santorini.
    
    if s.check() == sat:
        m = s.model()
        flight_vilnius_split = m[x1].as_long()      # Expected: 4
        flight_split_madrid = m[x2].as_long()         # Expected: 8  (4 + 5 - 1)
        flight_madrid_santorini = m[x3].as_long()     # Expected: 13 (8 + 6 - 1)
        
        itinerary = []
        # For each day in the 14-day trip, decide which city or cities you're in.
        # A day d is in a city's segment if it lies within the segment's start and end days.
        for day in range(1, 15):  # Days 1 to 14 inclusive
            places = []
            # Vilnius segment: from day 1 through day x1
            if 1 <= day <= flight_vilnius_split:
                places.append("Vilnius")
            # Split segment: from day x1 through day x2
            if flight_vilnius_split <= day <= flight_split_madrid:
                places.append("Split")
            # Madrid segment: from day x2 through day x3
            if flight_split_madrid <= day <= flight_madrid_santorini:
                places.append("Madrid")
            # Santorini segment: from day x3 through day 14
            if flight_madrid_santorini <= day <= 14:
                places.append("Santorini")
            
            itinerary.append({"day": day, "place": ", ".join(places)})
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()