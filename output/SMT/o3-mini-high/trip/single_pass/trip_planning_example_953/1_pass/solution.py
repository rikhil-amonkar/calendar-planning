from z3 import *
import json

def main():
    # We number our 7 cities as follows:
    # 0: Venice (5 days; also mandatory show from day 1 to 5)
    # 1: Salzburg (4 days)
    # 2: Stockholm (2 days)
    # 3: Barcelona (2 days)
    # 4: Florence (4 days)
    # 5: Frankfurt (4 days)
    # 6: Stuttgart (3 days)
    #
    # Flight connectivity (bidirectional, only direct flights allowed):
    # • Venice <-> Barcelona
    # • Venice <-> Stuttgart
    # • Venice <-> Frankfurt
    # • Barcelona <-> Frankfurt
    # • Barcelona <-> Florence
    # • Stockholm <-> Barcelona
    # • Frankfurt <-> Salzburg
    # • Frankfurt <-> Stockholm
    # • Stuttgart <-> Stockholm
    # • Stuttgart <-> Frankfurt
    # • (Also the symmetric edges)
    
    # For our model we set up:
    #   – An ordering variable "order" (an array of 7 integers, a permutation of 0..6)
    #       with the extra constraint that the first city must be Venice (index 0)
    #   – For each segment we have a “start day” s[i]. If we “fly” on the day s[i+1] from city i
    #       to city i+1 then that day is counted for both cities.
    #   – For a city visited in position i (with city index X), its number of days spent is:
    #       Duration(X) = required days. Its segment lasts from s[i] to e[i] where e[i] = s[i] + Duration(X) - 1.
    #   – We require that for each consecutive segment, the start day of the next equals the end day of the previous.
    #   – Since the double‐counted flight days “save” days, the total distinct days is:
    #         (sum of durations) – (# transitions) = 24 – 6 = 18.
    #   – Finally, we add the constraint that the last day of the trip is Day 18.
    
    # Create the solver.
    opt = Solver()
    
    # Create order variables, one per city in the itinerary.
    n = 7
    order = [Int(f"order_{i}") for i in range(n)]
    for o in order:
        opt.add(o >= 0, o < n)
    # The cities must all be different.
    opt.add(Distinct(order))
    # The first city must be Venice (index 0) to enable attending the show from Day 1-5.
    opt.add(order[0] == 0)
    
    # List of required durations by city index.
    durations = [5, 4, 2, 2, 4, 4, 3]
    # Corresponding city names.
    city_names = ["Venice", "Salzburg", "Stockholm", "Barcelona", "Florence", "Frankfurt", "Stuttgart"]
    
    # Allowed direct flight connections as pairs of (from, to).
    allowed_edges = [
        (0, 3), (3, 0),   # Venice <-> Barcelona
        (0, 6), (6, 0),   # Venice <-> Stuttgart
        (0, 5), (5, 0),   # Venice <-> Frankfurt
        (3, 5), (5, 3),   # Barcelona <-> Frankfurt
        (3, 4), (4, 3),   # Barcelona <-> Florence
        (2, 3), (3, 2),   # Stockholm <-> Barcelona
        (5, 1), (1, 5),   # Frankfurt <-> Salzburg
        (2, 5), (5, 2),   # Stockholm <-> Frankfurt
        (6, 2), (2, 6),   # Stuttgart <-> Stockholm
        (6, 5), (5, 6)    # Stuttgart <-> Frankfurt
    ]
    
    # For each successive pair in the itinerary, enforce that the flight is direct.
    for i in range(n - 1):
        # Build a disjunction over all allowed pairs.
        direct_conn = []
        for (a, b) in allowed_edges:
            direct_conn.append(And(order[i] == a, order[i+1] == b))
        opt.add(Or(direct_conn))
    
    # Create variables s[0] ... s[6] for the start day of each city's segment.
    s = [Int(f"s_{i}") for i in range(n)]
    # The trip starts on Day 1.
    opt.add(s[0] == 1)
    
    # Define a helper that returns the duration as a Z3 expression for a given city.
    def Duration(city):
        return If(city == 0, 5,
               If(city == 1, 4,
               If(city == 2, 2,
               If(city == 3, 2,
               If(city == 4, 4,
               If(city == 5, 4,
               If(city == 6, 3, 0)))))))
    
    # For each segment, let e[i] = s[i] + Duration(city) - 1 be the end day.
    # And for i from 0 to n-2, the next segment must start on the same day as the previous segment’s end.
    for i in range(n - 1):
        opt.add(s[i+1] == s[i] + Duration(order[i]) - 1)
    
    # The end day of the last segment must be Day 18.
    opt.add(s[n-1] + Duration(order[n-1]) - 1 == 18)
    
    # Solve.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n):
            # Determine the city index from the model.
            city_index = m.evaluate(order[i]).as_long()
            city = city_names[city_index]
            # Get the start day.
            start_day = m.evaluate(s[i]).as_long()
            # The required stay for that city.
            d_val = durations[city_index]
            end_day = start_day + d_val - 1
            itinerary.append({"city": city, "start_day": start_day, "end_day": end_day})
        
        # Produce a JSON output with the itinerary.
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()