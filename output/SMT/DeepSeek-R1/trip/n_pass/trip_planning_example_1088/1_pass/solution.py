from z3 import *
import json

def main():
    # Define the cities by indices for the middle part (c2 to c7)
    # 0: Oslo, 1: Stuttgart, 2: Split, 3: Geneva, 4: Tallinn, 5: Stockholm
    c = [Int('c2'), Int('c3'), Int('c4'), Int('c5'), Int('c6'), Int('c7')]
    s = Solver()

    # Each c[i] is between 0 and 5
    for i in range(6):
        s.add(And(c[i] >= 0, c[i] <= 5))
    
    # All distinct
    s.add(Distinct(c))

    # Adjacency list for the graph of the 6 cities (undirected)
    adj = {
        0: [2, 3, 4, 5],   # Oslo
        1: [2, 5],          # Stuttgart
        2: [0, 1, 3],       # Split
        3: [0, 2, 5],       # Geneva
        4: [0],             # Tallinn
        5: [0, 1, 2, 3]     # Stockholm
    }

    # Consecutive cities in the sequence must be connected
    for i in range(5):
        current = c[i]
        next_city = c[i+1]
        # next_city must be in the adjacency list of current
        s.add(Or([next_city == j for j in adj[current]]))

    # First flight: from Reykjavik to c2. Reykjavik is connected to Oslo(0), Stuttgart(1), Tallinn(4), Stockholm(5)
    s.add(Or(c[0] == 0, c[0] == 1, c[0] == 4, c[0] == 5))
    
    # Last flight: from c7 to Porto. Porto is connected to Oslo(0), Stuttgart(1), Geneva(3)
    s.add(Or(c[5] == 0, c[5] == 1, c[5] == 3))

    # Stockholm constraint: must be at c2 or c3
    st_at_c2 = (c[0] == 5)
    st_at_c3 = (c[1] == 5)
    s.add(Or(st_at_c2, st_at_c3))
    
    # If Stockholm is at c3, then c2 must be Split(2) or Geneva(3)
    s.add(If(st_at_c3, Or(c[0] == 2, c[0] == 3), True))

    if s.check() == sat:
        m = s.model()
        seq = [m.evaluate(c[i]) for i in range(6)]
        city_map = {
            0: "Oslo",
            1: "Stuttgart",
            2: "Split",
            3: "Geneva",
            4: "Tallinn",
            5: "Stockholm"
        }
        city_sequence = ["Reykjavik"] + [city_map[int(str(seq[i]))] for i in range(6)] + ["Porto"]
        
        days_map = {
            "Reykjavik": 2,
            "Oslo": 5,
            "Stuttgart": 5,
            "Split": 3,
            "Geneva": 2,
            "Porto": 3,
            "Tallinn": 5,
            "Stockholm": 3
        }
        
        starts = [1]  # Start at day1 for Reykjavik
        ends = [2]    # Reykjavik ends at day2 (2 days: day1 and day2)
        
        # Compute start and end days for the rest of the cities
        for i in range(1, 8):  # from the second city (index1) to Porto (index7)
            prev_end = ends[i-1]
            city = city_sequence[i]
            duration = days_map[city]
            start_i = prev_end  # because we arrive on the same day we leave the previous
            end_i = start_i + duration - 1
            starts.append(start_i)
            ends.append(end_i)
        
        itinerary = []
        for i in range(8):  # for each of the 8 cities
            L = starts[i]
            R = ends[i]
            city = city_sequence[i]
            if L == R:
                itinerary.append({"day_range": f"Day {L}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {L}-{R}", "place": city})
            # If this is not the last city, add the flight day records
            if i < 7:
                # Departure from current city on day R
                itinerary.append({"day_range": f"Day {R}", "place": city})
                # Arrival at next city on day R
                next_city = city_sequence[i+1]
                itinerary.append({"day_range": f"Day {R}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()