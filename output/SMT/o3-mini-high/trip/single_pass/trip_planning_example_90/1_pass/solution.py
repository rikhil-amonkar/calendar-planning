from z3 import Int, Solver, sat
import json

def main():
    # Define integer variables for start and end days (inclusive) for each city.
    start_nap = Int('start_nap')  # Naples start
    end_nap   = Int('end_nap')    # Naples end
    
    start_vie = Int('start_vie')  # Vienna start
    end_vie   = Int('end_vie')    # Vienna end
    
    start_vil = Int('start_vil')  # Vilnius start
    end_vil   = Int('end_vil')    # Vilnius end

    s = Solver()
    
    # We require the trip to go from day 1 to day 17.
    s.add(start_nap == 1)
    s.add(end_vil == 17)
    
    # Duration constraints:
    # Naples must be 5 days (if you fly from Naples on its last day, that day counts for Naples)
    s.add(end_nap - start_nap + 1 == 5)
    # Vienna must be 7 days.
    s.add(end_vie - start_vie + 1 == 7)
    # Vilnius must be 7 days.
    s.add(end_vil - start_vil + 1 == 7)
    
    # Flight (overlap) constraints:
    # When flying from Naples to Vienna the flight day is the last day in Naples and first in Vienna.
    s.add(end_nap == start_vie)
    # Likewise, when flying from Vienna to Vilnius the flight day overlaps.
    s.add(end_vie == start_vil)
    
    # Ordering (the intervals are contiguous in time)
    s.add(start_nap <= start_vie)
    s.add(start_vie <= start_vil)
    
    # Relatives condition: You plan to visit relatives in Naples between day 1 and 5.
    # This means the interval for Naples must overlap the window [1,5]. With start_nap==1, this is satisfied.
    s.add(start_nap <= 5)
    s.add(end_nap >= 1)
    
    if s.check() == sat:
        m = s.model()
        sn = m[start_nap].as_long()
        en = m[end_nap].as_long()
        sv = m[start_vie].as_long()
        ev = m[end_vie].as_long()
        svil = m[start_vil].as_long()
        evil = m[end_vil].as_long()
        
        # Build the itinerary day by day.
        # On a day that is a flight day the traveler is in both cities (we join the names with a slash).
        itinerary = []
        for day in range(1, evil + 1):
            places = []
            if sn <= day <= en:
                places.append("Naples")
            if sv <= day <= ev:
                places.append("Vienna")
            if svil <= day <= evil:
                places.append("Vilnius")
            itinerary.append({"day": day, "place": "/".join(places)})
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()