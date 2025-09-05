from z3 import *
import json

def main():
    solver = Solver()

    # There are 5 segments (cities) in the itinerary.
    # Cities indices: 0: "Hamburg" (2 days), 1: "Zurich" (3 days),
    # 2: "Helsinki" (2 days), 3: "Bucharest" (2 days), 4: "Split" (7 days)
    city_names = {0: "Hamburg", 1: "Zurich", 2: "Helsinki", 3: "Bucharest", 4: "Split"}
    # Fixed durations for each city.
    fixed_durations = {0: 2, 1: 3, 2: 2, 3: 2, 4: 7}

    num_segments = 5

    # Create Z3 Int variables for each segment's city choice.
    cities = [Int(f"city_{i}") for i in range(num_segments)]
    for c in cities:
        solver.add(c >= 0, c <= 4)
    # All visited cities must be distinct.
    solver.add(Distinct(cities))

    # Create variables for durations (these depend on the chosen city)
    durs = [Int(f"dur_{i}") for i in range(num_segments)]
    for i in range(num_segments):
        solver.add(
            If(cities[i] == 0, durs[i] == fixed_durations[0],
            If(cities[i] == 1, durs[i] == fixed_durations[1],
            If(cities[i] == 2, durs[i] == fixed_durations[2],
            If(cities[i] == 3, durs[i] == fixed_durations[3],
            If(cities[i] == 4, durs[i] == fixed_durations[4],
               False)))))  # Should never get here

    # Create variables for start and end day of each segment.
    # If a flight is taken on day X, then that day counts for both the departing and arriving cities.
    # So we set up the segments so that for segment i:
    #   end_i = start_i + dur_i - 1, and for i > 0, start_i = end_{i-1}.
    starts = [Int(f"start_{i}") for i in range(num_segments)]
    ends   = [Int(f"end_{i}") for i in range(num_segments)]

    # The trip starts on day 1.
    solver.add(starts[0] == 1)
    for i in range(num_segments):
        solver.add(ends[i] == starts[i] + durs[i] - 1)
        if i > 0:
            solver.add(starts[i] == ends[i-1])
    # Total unique trip days is 12.
    solver.add(ends[num_segments - 1] == 12)

    # Special participant constraints:
    # 1. Wedding in Zurich must be attended between day 1 and day 3.
    #    If a segment is in Zurich (city 1), then its start day must be <= 3.
    for i in range(num_segments):
        solver.add(Implies(cities[i] == 1, starts[i] <= 3))

    # 2. Conference in Split is on day 4 and day 10.
    #    For a segment in Split (city 4), because its duration is 7 days,
    #    the only way to cover days 4 and 10 is for the segment to start exactly on day 4.
    for i in range(num_segments):
        solver.add(Implies(cities[i] == 4, starts[i] == 4))

    # Direct flight connections allowed (bidirectional):
    # Allowed pairs (unordered):
    #   {Hamburg, Zurich} -> (0,1)
    #   {Hamburg, Helsinki} -> (0,2)
    #   {Hamburg, Bucharest} -> (0,3)
    #   {Hamburg, Split} -> (0,4)
    #   {Zurich, Helsinki} -> (1,2)
    #   {Zurich, Bucharest} -> (1,3)
    #   {Zurich, Split} -> (1,4)
    #   {Helsinki, Split} -> (2,4)
    def flight_allowed(a, b):
        return Or(
            And(a == 0, b == 1), And(a == 1, b == 0),
            And(a == 0, b == 2), And(a == 2, b == 0),
            And(a == 0, b == 3), And(a == 3, b == 0),
            And(a == 0, b == 4), And(a == 4, b == 0),
            And(a == 1, b == 2), And(a == 2, b == 1),
            And(a == 1, b == 3), And(a == 3, b == 1),
            And(a == 1, b == 4), And(a == 4, b == 1),
            And(a == 2, b == 4), And(a == 4, b == 2)
        )

    # For each flight between consecutive segments, enforce direct flight.
    for i in range(num_segments - 1):
        solver.add(flight_allowed(cities[i], cities[i+1]))

    # Solve the SMT model.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_segments):
            s_val = model[starts[i]].as_long()
            e_val = model[ends[i]].as_long()
            city_val = model[cities[i]].as_long()
            itinerary.append({
                "day_range": f"Day {s_val}-{e_val}",
                "place": city_names[city_val]
            })
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}

    print(json.dumps(result))

if __name__ == "__main__":
    main()