from z3 import *
import json

def main():
    s = Solver()

    # We split the 13‐day trip into 4 contiguous segments.
    # A flight day is the overlap day of two consecutive segments.
    # If S1 = [1, a], S2 = [a, b], S3 = [b, c] and S4 = [c, 13],
    # then the “city‐days” add up to:
    #   L1 + L2 + L3 + L4
    # = (a - 1 + 1) + (b - a + 1) + (c - b + 1) + (13 - c + 1)
    # = 13 + 3 = 16.
    #
    # The required city‐days are:
    #   Madrid = 4, Seville = 2, Porto = 3 and Stuttgart = 7.
    # Their sum is 16. Hence each segment must be assigned to one city,
    # and the double‐counting (flight days) makes the total itinerary only 13 days.
    #
    # Moreover, we have additional constraints:
    #   • Conference in Stuttgart must be attended on day 7 and day 13.
    #     (That forces the segment that covers day 13 to be Stuttgart.
    #      In fact, only the last segment covers day 13.)
    #   • You plan to visit relatives in Madrid between day 1 and day 4.
    #     (So some segment overlapping days 1–4 must be Madrid.)
    #
    # Note: When you fly, the flight day belongs to both the departing and arriving segments.
    #
    # We fix the segmentation as follows:
    #   S1 = [1, a] with length L1 = a
    #   S2 = [a, b] with length L2 = b - a + 1
    #   S3 = [b, c] with length L3 = c - b + 1
    #   S4 = [c, 13] with length L4 = 13 - c + 1 = 14 - c
    #
    # Since the city-days must sum to 16 and 16 = 13 + (#flights)=13 + 3,
    # we have 4 segments. Also, because day 13 must be Stuttgart and only S4 covers day 13,
    # S4 must be Stuttgart. In our model we force:
    #   S4: length = 7 AND its interval must include day 7 too.
    # In order for day 7 to be in S4, we need c <= 7.
    # But also if S4’s length is 14-c=7 then c = 7.
    #
    # We therefore set:
    #   c = 7.
    #
    # And the remaining boundaries satisfy: 1 < a < b < c = 7.
    #
    # The assignment of required days to segments must be:
    #   Madrid: 4 days, Seville: 2 days, Porto: 3 days, Stuttgart: 7 days.
    #
    # We now represent the following:
    #
    # Variables:
    #   a, b: integers with 1 < a < b < 7.
    #   c is fixed to 7.
    #   cities[i] : for segment i (0-based indexing for S1...S4)
    #       0 → Madrid
    #       1 → Seville
    #       2 → Porto
    #       3 → Stuttgart
    #
    # Constraints:
    # 1. Each city appears exactly once (Distinct).
    # 2. S4 must be Stuttgart, i.e. cities[3] == 3.
    # 3. The required length per segment is given by:
    #      S1: L1 = a,
    #      S2: L2 = b - a + 1,
    #      S3: L3 = 7 - b + 1 = 8 - b,
    #      S4: L4 = 14 - 7 = 7.
    #    And they must equal:
    #      if city is Madrid (0): 4,
    #      if Seville (1): 2,
    #      if Porto (2): 3,
    #      if Stuttgart (3): 7.
    #
    # 4. Allowed direct flights (transitions) are only between:
    #      • Madrid and Seville
    #      • Madrid and Porto
    #      • Seville and Porto
    #      • Porto and Stuttgart
    #    (Flights are bidirectional.)
    #
    #    Thus, between consecutive segments i and i+1, (cities[i], cities[i+1])
    #    must be one of the allowed pairs.
    #
    # 5. Visit relatives in Madrid between day 1 and day 4:
    #    At least one segment overlapping days 1–4 must be Madrid.
    #    Note: S1 always covers day 1, and S1’s interval is [1, a].
    #          For S2, the overlap happens if a <= 4; for S3 it is if b <= 4.
    
    # Define segmentation boundaries
    a = Int('a')
    b = Int('b')
    c = 7  # fixed so that S4 = [7, 13], length 7, and day 7 is in S4
    
    s.add(a > 1, a < b, b < c)  # 1 < a < b < 7
    
    # Define city assignment for each segment: 0:Madrid, 1:Seville, 2:Porto, 3:Stuttgart.
    cities = [Int(f"city_{i}") for i in range(4)]
    for ci in cities:
        s.add(And(ci >= 0, ci <= 3))
    s.add(Distinct(cities))
    
    # The last segment S4 must be Stuttgart.
    s.add(cities[3] == 3)
    
    # Segment lengths
    L1 = a                  # S1 = [1, a]
    L2 = b - a + 1          # S2 = [a, b]
    L3 = 8 - b              # S3 = [b, 7] since 7 - b +1 = 8-b
    L4 = 7                  # S4 = [7, 13] (13 - 7 + 1)
    
    # Required durations: Madrid:4, Seville:2, Porto:3, Stuttgart:7.
    def length_constraint(seg_length, city_var):
        return If(city_var == 0, seg_length == 4,
                  If(city_var == 1, seg_length == 2,
                     If(city_var == 2, seg_length == 3,
                        seg_length == 7)))  # For city_var == 3 (Stuttgart)
    
    s.add(length_constraint(L1, cities[0]))
    s.add(length_constraint(L2, cities[1]))
    s.add(length_constraint(L3, cities[2]))
    # S4 already has length 7 and is Stuttgart.
    
    # Allowed direct flights between consecutive segments.
    # Allowed pairs: (Madrid,Seville), (Madrid,Porto), (Seville,Porto), (Porto,Stuttgart)
    def allowed(c1, c2):
        return Or(And(c1 == 0, c2 == 1),
                  And(c1 == 1, c2 == 0),
                  And(c1 == 0, c2 == 2),
                  And(c1 == 2, c2 == 0),
                  And(c1 == 1, c2 == 2),
                  And(c1 == 2, c2 == 1),
                  And(c1 == 2, c2 == 3),
                  And(c1 == 3, c2 == 2))
    
    s.add(allowed(cities[0], cities[1]))
    s.add(allowed(cities[1], cities[2]))
    s.add(allowed(cities[2], cities[3]))
    
    # Ensure that you visit relatives in Madrid between day 1 and day 4.
    # S1 always covers day 1. S2 covers [a, b] provided a <= 4,
    # S3 covers [b, 7] provided b <= 4.
    s.add(Or(cities[0] == 0,
             And(cities[1] == 0, a <= 4),
             And(cities[2] == 0, b <= 4)))
    
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        
        # Get the assigned city values for each segment
        segs = [m[cities[i]].as_long() for i in range(4)]
        city_map = {0: "Madrid", 1: "Seville", 2: "Porto", 3: "Stuttgart"}
        
        # Define segments with their intervals.
        # S1: days 1 to a_val
        # S2: days a_val to b_val
        # S3: days b_val to 7    (note: 7 is both the end of S3 and the start of S4)
        # S4: days 7 to 13
        segments = [
            {"city": city_map[segs[0]], "start": 1, "end": a_val},
            {"city": city_map[segs[1]], "start": a_val, "end": b_val},
            {"city": city_map[segs[2]], "start": b_val, "end": 7},
            {"city": city_map[segs[3]], "start": 7, "end": 13}
        ]
        
        # Build the day-by-day itinerary.
        itinerary = []
        for day in range(1, 14):
            # A day may fall in the overlap of two segments (i.e. flight day).
            places = []
            for seg in segments:
                if seg["start"] <= day <= seg["end"]:
                    places.append(seg["city"])
            # Remove any duplicates (shouldn't happen, but extra safety).
            places = list(dict.fromkeys(places))
            # If there's only one city, output it as a string;
            # if two (a flight day) output as a list.
            day_entry = {"day": day, "place": places[0] if len(places) == 1 else places}
            itinerary.append(day_entry)
        
        # Output the itinerary as JSON.
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()