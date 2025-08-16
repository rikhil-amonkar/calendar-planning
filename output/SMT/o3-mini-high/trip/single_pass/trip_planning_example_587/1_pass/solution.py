from z3 import Solver, Int, Distinct, If, Or
import json

def solve_schedule():
    # We have 5 cities with fixed durations:
    #  Index : City        Duration (days)
    #    0   : Manchester  3
    #    1   : Istanbul    7
    #    2   : Venice      7
    #    3   : Krakow      6
    #    4   : Lyon        2
    #
    # Important events:
    #   – Wedding in Manchester must occur between day 1 and day 3.
    #   – Workshop in Venice must occur between day 3 and day 9.
    #
    # When flying from one city to the next the flight day is shared by both.
    # Thus the sum of the city‐durations (3+7+7+6+2 = 25) minus the 4 overlaps equals 21 total days.
    #
    # Flight connections (bidirectional) exist only between:
    #    Manchester – Venice
    #    Manchester – Istanbul
    #    Venice – Istanbul
    #    Istanbul – Krakow
    #    Venice – Lyon
    #    Lyon – Istanbul
    #    Manchester – Krakow
    #
    # We will decide an ordering of the five city visits. Let pos[0] ... pos[4] be an ordering,
    # and let start_vars[i] be the start day (in the overall 21–day itinerary) of segment i.
    # The segment for a city lasts exactly its given duration; however, when two segments are consecutive,
    # the flight day (which is the last day of the earlier segment and the first day of the next) is common.
    
    solver = Solver()
    
    # Create 5 integer variables for positions (the city assigned to segment i).
    pos = [Int(f"pos_{i}") for i in range(5)]
    # Create 5 integer variables for the start day of each segment.
    starts = [Int(f"start_{i}") for i in range(5)]
    
    # City data: index -> (name, duration)
    city_names = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    durations_list = [3, 7, 7, 6, 2]
    
    # Constrain each pos[i] to be between 0 and 4 and all distinct (each city is visited exactly once)
    for i in range(5):
        solver.add(pos[i] >= 0, pos[i] <= 4)
        # The start days must be at least day 1 and no later than day 21.
        solver.add(starts[i] >= 1, starts[i] <= 21)
    solver.add(Distinct(pos[0], pos[1], pos[2], pos[3], pos[4]))
    
    # Define a function to obtain the duration corresponding to a city variable
    def duration_for(city_var):
        return If(city_var == 0, durations_list[0],
               If(city_var == 1, durations_list[1],
               If(city_var == 2, durations_list[2],
               If(city_var == 3, durations_list[3],
               If(city_var == 4, durations_list[4], 0)))))
    
    # The itinerary is contiguous.
    # The first segment starts on day 1.
    solver.add(starts[0] == 1)
    # For each segment i (0<=i<=3), the next segment begins on the common flight day,
    # i.e. start[i+1] = (start[i] + duration(segment_i) - 1).
    for i in range(4):
        solver.add(starts[i+1] == starts[i] + duration_for(pos[i]) - 1)
    # The triple overlap condition: the end day of the last segment equals 21.
    solver.add(starts[4] + duration_for(pos[4]) - 1 == 21)
    
    # Flight connections: For consecutive segments, the two cities must be connected.
    # Allowed pairs (a,b) (note the flights are bidirectional):
    #   (Manchester, Venice), (Manchester, Istanbul), (Manchester, Krakow),
    #   (Venice, Istanbul), (Venice, Lyon),
    #   (Istanbul, Krakow), (Istanbul, Venice), (Istanbul, Manchester), (Istanbul, Lyon),
    #   (Krakow, Istanbul), (Krakow, Manchester),
    #   (Lyon, Venice), (Lyon, Istanbul)
    def allowed_transition(a, b):
        return Or(
            # Manchester (0) and Venice (2)
            Or(And(a == 0, b == 2), And(a == 2, b == 0)),
            # Manchester and Istanbul (1)
            Or(And(a == 0, b == 1), And(a == 1, b == 0)),
            # Manchester and Krakow (3)
            Or(And(a == 0, b == 3), And(a == 3, b == 0)),
            # Venice (2) and Istanbul (1)
            Or(And(a == 2, b == 1), And(a == 1, b == 2)),
            # Venice and Lyon (4)
            Or(And(a == 2, b == 4), And(a == 4, b == 2)),
            # Istanbul and Krakow (3)
            Or(And(a == 1, b == 3), And(a == 3, b == 1)),
            # Istanbul and Lyon (4)
            Or(And(a == 1, b == 4), And(a == 4, b == 1))
        )
    
    for i in range(4):
        solver.add(allowed_transition(pos[i], pos[i+1]))
    
    # Event constraints:
    #  1. Wedding in Manchester: The wedding must occur between day 1 and day 3.
    #     We force that if a segment is Manchester (city index 0), its start day must be at most 3.
    for i in range(5):
        solver.add(If(pos[i] == 0, starts[i] <= 3, True))
    
    #  2. Workshop in Venice: Must occur between day 3 and day 9.
    #     For the Venice segment (city index 2), require its start day to be at most 9.
    for i in range(5):
        solver.add(If(pos[i] == 2, starts[i] <= 9, True))
    
    # Solve the constraints.
    if solver.check() == 'sat' or solver.check() == 1:
        m = solver.model()
        # Reconstruct the ordered segments:
        segments = []
        for i in range(5):
            city_idx = m.evaluate(pos[i]).as_long()
            city = city_names[city_idx]
            seg_start = m.evaluate(starts[i]).as_long()
            seg_duration = durations_list[city_idx]
            seg_end = seg_start + seg_duration - 1
            segments.append((seg_start, seg_end, city))
        # For clarity, sort segments by start (they should already be in order)
        segments.sort(key=lambda x: x[0])
    
        # Build the full itinerary for days 1..21.
        # Note: A day that is a "flight day" (i.e. the common day connecting two segments)
        # will be covered by two segments. We list both cities (separated by a comma).
        itinerary = []
        for day in range(1, 22):
            cities_today = []
            for (s_day, e_day, city) in segments:
                if s_day <= day <= e_day:
                    cities_today.append(city)
            # If more than one city is active this day, join them with a comma.
            place = ", ".join(cities_today)
            itinerary.append({"day": day, "place": place})
    
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    solve_schedule()