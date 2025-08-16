from z3 import *
import json

def main():
    # Define the cities and required lengths.
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    # Required days if staying in the city.
    durations = [2, 5, 5, 3, 2, 4, 3, 2]
    n = len(cities)  # 8
    num_segments = n  # each city appears exactly once in some order

    # We will represent the itinerary as an ordered sequence of segments.
    # Each segment i has:
    #   • an associated city indicated by "order[i]" (an integer 0..7 mapping to cities list)
    #   • a start day s[i] and an end day e[i] (both integers).
    # Note that if a flight occurs on a day then that day is counted in two segments.
    # The conditions are:
    #   s[0] = 1 and for i>0, s[i] = e[i-1] (the flight day overlap)
    #   and for each segment i, e[i] = s[i] + (duration for that city) - 1.
    # Total distinct days in the trip (the last day of the last segment) is 19.

    # Create Z3 integer variables.
    order = [Int("order_%d" % i) for i in range(num_segments)]
    s = [Int("s_%d" % i) for i in range(num_segments)]
    e = [Int("e_%d" % i) for i in range(num_segments)]

    solver = Solver()

    # 1. Order constraints: each order[i] in 0..7 and all are distinct.
    for i in range(num_segments):
        solver.add(order[i] >= 0, order[i] < n)
    solver.add(Distinct(order))
    
    # Special: You must meet your friend in Tallinn between day 1 and day 2.
    # Since flight overlap prevents a later appearance from covering day 1-2,
    # we force Tallinn (index 4) to be the first segment.
    solver.add(order[0] == 4)

    # 2. Timing constraints.
    # The first day is fixed.
    solver.add(s[0] == 1)
    # We write a helper that “selects” the duration of a segment according to the city.
    def seg_duration(i):
        return If(order[i] == 0, durations[0],
               If(order[i] == 1, durations[1],
               If(order[i] == 2, durations[2],
               If(order[i] == 3, durations[3],
               If(order[i] == 4, durations[4],
               If(order[i] == 5, durations[5],
               If(order[i] == 6, durations[6],
               If(order[i] == 7, durations[7],
                  0)))))))
    
    # For each segment, the end day is the start day plus (duration - 1).
    # Also, for i>0, the start day equals the previous segment’s end day.
    for i in range(num_segments):
        solver.add(e[i] == s[i] + seg_duration(i) - 1)
        if i > 0:
            solver.add(s[i] == e[i-1])
    # Total trip lasts 19 days (the end day of the last segment is day 19).
    solver.add(e[num_segments - 1] == 19)

    # 3. Flight connection constraints.
    # A flight occurs between consecutive segments. If you fly on day X,
    # that day counts for both the departure and arrival cities.
    # The only allowed direct flights are (in either direction):
    #   Dubrovnik–Stockholm, Lisbon–Copenhagen, Lisbon–Lyon, Copenhagen–Stockholm,
    #   Copenhagen–Split, Prague–Stockholm, Tallinn–Stockholm, Prague–Lyon, Lisbon–Stockholm,
    #   Prague–Lisbon, Stockholm–Split, Prague–Copenhagen, Split–Lyon,
    #   Copenhagen–Dubrovnik, Prague–Split, Tallinn–Copenhagen, Tallinn–Prague.
    #
    # We map the cities to indices as follows:
    #   0: Lisbon, 1: Dubrovnik, 2: Copenhagen, 3: Prague,
    #   4: Tallinn, 5: Stockholm, 6: Split, 7: Lyon.
    #
    # First we express the allowed unordered pairs (using sorted order).
    allowed_pairs = [
        (0,2),  # Lisbon–Copenhagen
        (0,3),  # Lisbon–Prague (flight Lisbon–Prague is allowed)
        (0,5),  # Lisbon–Stockholm
        (0,7),  # Lisbon–Lyon
        (1,2),  # Dubrovnik–Copenhagen (via Copenhagen–Dubrovnik)
        (1,5),  # Dubrovnik–Stockholm
        (2,3),  # Copenhagen–Prague
        (2,4),  # Tallinn–Copenhagen (order: 2 and 4)
        (2,5),  # Copenhagen–Stockholm
        (2,6),  # Copenhagen–Split
        (3,4),  # Tallinn–Prague (order: 3 and 4)
        (3,5),  # Prague–Stockholm
        (3,6),  # Prague–Split
        (3,7),  # Prague–Lyon
        (4,5),  # Tallinn–Stockholm
        (5,6),  # Stockholm–Split
        (6,7)   # Split–Lyon
    ]
    # For every consecutive pair of segments, ensure that the two cities have a direct flight.
    for i in range(num_segments - 1):
        a = order[i]
        b = order[i+1]
        mini = If(a < b, a, b)
        maxi = If(a < b, b, a)
        # Create a disjunction that (mini, maxi) equals one of the allowed pairs.
        conds = [And(mini == p, maxi == q) for (p, q) in allowed_pairs]
        solver.add(Or(conds))
    
    # 4. Special event date constraints in certain cities.
    for i in range(num_segments):
        # Workshop in Lisbon must be attended on either day 4 or day 5.
        solver.add(Implies(order[i] == 0, 
                           Or(And(s[i] <= 4, 4 <= e[i]),
                              And(s[i] <= 5, 5 <= e[i]))))
        # Wedding in Stockholm must occur on some day between 13 and 16.
        solver.add(Implies(order[i] == 5,
                           Or(And(s[i] <= 13, 13 <= e[i]),
                              And(s[i] <= 14, 14 <= e[i]),
                              And(s[i] <= 15, 15 <= e[i]),
                              And(s[i] <= 16, 16 <= e[i]))))
        # Annual show in Lyon must be attended on day 18 or day 19.
        solver.add(Implies(order[i] == 7,
                           Or(And(s[i] <= 18, 18 <= e[i]),
                              And(s[i] <= 19, 19 <= e[i]))))
        # Friend meet in Tallinn must occur between day 1 and day 2.
        # (Since we force Tallinn to be the first segment, this will be satisfied.)
        solver.add(Implies(order[i] == 4,
                           Or(And(s[i] <= 1, 1 <= e[i]),
                              And(s[i] <= 2, 2 <= e[i]))))

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        seg_order = [model.evaluate(order[i]).as_long() for i in range(num_segments)]
        seg_s = [model.evaluate(s[i]).as_long() for i in range(num_segments)]
        seg_e = [model.evaluate(e[i]).as_long() for i in range(num_segments)]
        
        # Build a list with the segments and their city names, start and end days.
        segments = []
        for i in range(num_segments):
            segments.append({
                "city": cities[seg_order[i]],
                "start": seg_s[i],
                "end": seg_e[i]
            })

        # Reconstruct the daily itinerary.
        # For each day d in the overall trip (days 1 to 19), find those segments for which d is in [start, end].
        # (On a flight day d there will be two segments – one ending and one starting – so d appears for both cities.)
        day_itinerary = []
        for d in range(1, 20):
            cities_today = []
            for seg in segments:
                if seg["start"] <= d <= seg["end"]:
                    cities_today.append(seg["city"])
            day_itinerary.append({"day": d, "cities": cities_today})
        
        # Output the itinerary as a JSON dictionary.
        output = {"itinerary": day_itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()