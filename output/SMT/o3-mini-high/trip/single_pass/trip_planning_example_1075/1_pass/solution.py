from z3 import *
import json

def main():
    solver = Solver()

    num_segments = 8

    # The eight cities 0--7:
    # 0: Vienna, 1: Lyon, 2: Edinburgh, 3: Reykjavik,
    # 4: Stuttgart, 5: Manchester, 6: Split, 7: Prague
    city_names = {0:"Vienna", 1:"Lyon", 2:"Edinburgh", 3:"Reykjavik",
                  4:"Stuttgart", 5:"Manchester", 6:"Split", 7:"Prague"}
    # Required days per city
    durations = {0:4, 1:3, 2:4, 3:5, 4:5, 5:2, 6:5, 7:4}

    # Create an array "order" for the order in which the cities are visited.
    order = [Int(f"order_{i}") for i in range(num_segments)]
    for i in range(num_segments):
        solver.add(order[i] >= 0, order[i] < 8)
    solver.add(Distinct(order))

    # Create an array s[] for start days of each segment.
    s = [Int(f"s_{i}") for i in range(num_segments)]
    # The first city starts on day 1.
    solver.add(s[0] == 1)

    # A helper function: given a Z3 expression for a city, return its duration.
    def dur(city):
        return If(city == 0, durations[0],
               If(city == 1, durations[1],
               If(city == 2, durations[2],
               If(city == 3, durations[3],
               If(city == 4, durations[4],
               If(city == 5, durations[5],
               If(city == 6, durations[6],
               If(city == 7, durations[7], 0)))))))

    # For each segment i, the segment covers days s[i] to s[i] + (duration - 1).
    # The flight rule lets us “overlap” so that for i>=1, we set s[i] equal to the previous segment’s end day.
    for i in range(num_segments - 1):
        solver.add(s[i+1] == s[i] + dur(order[i]) - 1)
    # Final constraint: the last city’s end day is day 25.
    solver.add(s[num_segments-1] + dur(order[num_segments-1]) - 1 == 25)

    # Allowed flight transitions (remember: flying on day X puts you in BOTH cities on day X):
    def allowed(a, b):
        return Or(
            And(a == 3, b == 4),                # Reykjavik -> Stuttgart
            And(a == 4, b == 6), And(a == 6, b == 4),  # Stuttgart and Split (both ways)
            And(a == 4, b == 0), And(a == 0, b == 4),  # Stuttgart and Vienna
            And(a == 7, b == 5), And(a == 5, b == 7),  # Prague and Manchester
            And(a == 2, b == 7), And(a == 7, b == 2),  # Edinburgh and Prague
            And(a == 5, b == 6),                # from Manchester to Split (directional)
            And(a == 7, b == 0), And(a == 0, b == 7),  # Prague and Vienna
            And(a == 0, b == 5), And(a == 5, b == 0),  # Vienna and Manchester
            And(a == 7, b == 6), And(a == 6, b == 7),  # Prague and Split
            And(a == 0, b == 1), And(a == 1, b == 0),  # Vienna and Lyon
            And(a == 4, b == 2), And(a == 2, b == 4),  # Stuttgart and Edinburgh
            And(a == 6, b == 1), And(a == 1, b == 6),  # Split and Lyon
            And(a == 4, b == 5), And(a == 5, b == 4),  # Stuttgart and Manchester
            And(a == 7, b == 1), And(a == 1, b == 7),  # Prague and Lyon
            And(a == 3, b == 0), And(a == 0, b == 3),  # Reykjavik and Vienna
            And(a == 7, b == 3), And(a == 3, b == 7),  # Prague and Reykjavik
            And(a == 0, b == 6), And(a == 6, b == 0)   # Vienna and Split
        )
    # Add flight connectivity constraint between every consecutive pair.
    for i in range(num_segments - 1):
        solver.add(allowed(order[i], order[i+1]))

    # Special scheduling constraints:
    # (1) Edinburgh (city 2) must cover days 5–8.
    #     Since its required duration is 4, and if flown in on day X then X is counted for it,
    #     we force its segment to start on day 5.
    for i in range(num_segments):
        solver.add(Implies(order[i] == 2, s[i] == 5))
    # (2) Split (city 6) must have at least one day between day 19 and day 23.
    #     With required duration 5 (covering days s to s+4), we require its start day to satisfy: s∈[15,23]
    for i in range(num_segments):
        solver.add(Implies(order[i] == 6, And(s[i] >= 15, s[i] <= 23)))
    
    # Solve the model.
    if solver.check() == sat:
        m = solver.model()
        
        # Build the itinerary as a list of segments.
        segments = []
        for i in range(num_segments):
            city_val = m.evaluate(order[i]).as_long()
            start_day = m.evaluate(s[i]).as_long()
            d = durations[ city_val ]
            end_day = start_day + d - 1
            segments.append({"city": city_names[city_val],
                             "start_day": start_day,
                             "end_day": end_day})
        
        # For clarity the printed itinerary is given as one segment per visited city.
        # (Remember: on flight days the day counts for both segments, see the example:
        #  “Venice: Day 1–3, Vienna: Day 3–6”)
        result = {"itinerary": segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()