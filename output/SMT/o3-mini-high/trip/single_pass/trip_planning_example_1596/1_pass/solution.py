from z3 import *
import json

# Our cities (by index) and required durations:
# 0: Bucharest (2 days)
# 1: Krakow    (4 days)
# 2: Munich    (3 days)   --> also must include a workshop between day 18 and day 20
# 3: Barcelona (5 days)
# 4: Warsaw    (5 days)   --> must include conference on day 25 and day 29 =>
#                          Warsaw’s visit must be exactly days 25–29.
# 5: Budapest  (5 days)   --> must cover day 9 through 13 (annual show)
# 6: Stockholm (2 days)   --> must meet friend between day 17 and 18
# 7: Riga      (5 days)
# 8: Edinburgh (5 days)   --> must meet friend between day 1 and 5
# 9: Vienna    (5 days)

city_names = {
    0: "Bucharest",
    1: "Krakow",
    2: "Munich",
    3: "Barcelona",
    4: "Warsaw",
    5: "Budapest",
    6: "Stockholm",
    7: "Riga",
    8: "Edinburgh",
    9: "Vienna"
}

# Duration function: returns the fixed number of days for a given city.
def Duration(city):
    return If(city == 0, 2,
           If(city == 1, 4,
           If(city == 2, 3,
           If(city == 3, 5,
           If(city == 4, 5,
           If(city == 5, 5,
           If(city == 6, 2,
           If(city == 7, 5,
           If(city == 8, 5,
           If(city == 9, 5, 0))))))))))

# Allowed direct flight connections (treating flights as undirected).
# Our mapping for cities is as above.
allowed_pairs = [
    (0,2),   # Munich and Bucharest
    (0,3),   # Barcelona and Bucharest
    (0,4),   # Bucharest and Warsaw
    (0,5),   # Budapest and Bucharest
    (0,7),   # Bucharest and Riga
    (0,9),   # Vienna and Bucharest
    (1,2),   # Munich and Krakow
    (1,3),   # Barcelona and Krakow
    (1,4),   # Warsaw and Krakow
    (1,6),   # Stockholm and Krakow
    (1,8),   # Edinburgh and Krakow
    (1,9),   # Vienna and Krakow
    (2,3),   # Barcelona and Munich
    (2,4),   # Munich and Warsaw
    (2,5),   # Budapest and Munich
    (2,6),   # Stockholm and Munich
    (2,7),   # from Riga to Munich
    (2,8),   # Edinburgh and Munich
    (2,9),   # Vienna and Munich
    (3,5),   # Barcelona and Budapest
    (3,6),   # Barcelona and Stockholm
    (3,7),   # Barcelona and Riga
    (3,8),   # Edinburgh and Barcelona
    (3,9),   # Barcelona and Vienna
    (4,5),   # Budapest and Warsaw
    (4,6),   # Stockholm and Warsaw
    (4,7),   # Riga and Warsaw
    (4,9),   # Vienna and Warsaw
    (5,8),   # Edinburgh and Budapest
    (5,9),   # Budapest and Vienna
    (6,7),   # Stockholm and Riga
    (6,8),   # Edinburgh and Stockholm
    (6,9),   # Vienna and Stockholm
    (7,8),   # Edinburgh and Riga
    (7,9)    # Vienna and Riga
]

def flight_allowed(a, b):
    # Return a Z3 boolean expression that a and b (city indices) are connected.
    conds = []
    for (u,v) in allowed_pairs:
        # Since flights are undirected, either (a==u and b==v) or (a==v and b==u) is allowed.
        conds.append(And(a == u, b == v))
        conds.append(And(a == v, b == u))
    return Or(conds)

def main():
    opt = Solver()

    # There will be a permutation P of the 10 cities representing the visiting order.
    P = [Int(f"P_{i}") for i in range(10)]
    for i in range(10):
        opt.add(And(P[i] >= 0, P[i] <= 9))
    opt.add(Distinct(P))

    # S[i] will be the starting day of the visit to city P[i].
    S_days = [Int(f"S_{i}") for i in range(10)]
    # The first visit always begins on day 1.
    opt.add(S_days[0] == 1)
    # Unroll the itinerary: if you are in city P[i] for Duration(P[i]) days (counting the flight overlap),
    # then the next city’s start day is:
    #    S[i+1] = S[i] + Duration(P[i]) - 1.
    for i in range(9):
        opt.add(S_days[i+1] == S_days[i] + Duration(P[i]) - 1)

    # Total trip timeline: The last city must finish on day 32.
    opt.add(S_days[9] + Duration(P[9]) - 1 == 32)

    # Add extra day constraints according to the problem:
    # • Budapest (city index 5) must cover day 9–13 exactly.
    for i in range(10):
        opt.add(Implies(P[i] == 5, S_days[i] == 9))
    # • Warsaw (4) must cover days 25–29.
    for i in range(10):
        opt.add(Implies(P[i] == 4, S_days[i] == 25))
    # • Edinburgh (8) – meet friend between day 1 and 5:
    for i in range(10):
        opt.add(Implies(P[i] == 8, S_days[i] <= 5))
    # • Stockholm (6) – meet friends between day 17 and 18.
    # Since its duration is 2 days, we require that its interval [S, S+1] covers day 17 or 18;
    # this is achieved by: S_days in {16,17,18} (if S==16 then days 16–17; if S==18 then days 18–19).
    for i in range(10):
        opt.add(Implies(P[i] == 6, And(S_days[i] >= 16, S_days[i] <= 18)))
    # • Munich (2) – workshop between day 18 and 20.
    # With duration 3 the interval is [S, S+2] so we require S_days in [16,20].
    for i in range(10):
        opt.add(Implies(P[i] == 2, And(S_days[i] >= 16, S_days[i] <= 20)))
    # (For Budapest and Warsaw the “shows” force the only possible intervals.)

    # Flight constraints:
    # For each consecutive pair in the visit order, the two cities must be connected by a direct flight.
    for i in range(9):
        opt.add(flight_allowed(P[i], P[i+1]))
    
    # Solve the constraints.
    if opt.check() == sat:
        m = opt.model()
        # Retrieve the order and starting times.
        order = [m.evaluate(P[i]).as_long() for i in range(10)]
        starts = [m.evaluate(S_days[i]).as_long() for i in range(10)]
        # Also compute each segment’s duration from our Duration function.
        seg_duration = []
        for i in range(10):
            # Use the mapping (since Duration is fully determined by the city index)
            city = order[i]
            if city in [0]:    d = 2
            elif city in [1]:  d = 4
            elif city in [2]:  d = 3
            elif city in [3]:  d = 5
            elif city in [4]:  d = 5
            elif city in [5]:  d = 5
            elif city in [6]:  d = 2
            elif city in [7]:  d = 5
            elif city in [8]:  d = 5
            elif city in [9]:  d = 5
            seg_duration.append(d)
        segments = []
        for i in range(10):
            seg_start = starts[i]
            seg_end = seg_start + seg_duration[i] - 1
            segments.append((seg_start, seg_end, order[i]))

        # Reconstruct the itinerary.
        # We produce a mapping for each day (1 to 32).
        # When a flight happens (which means that day is the start of a segment other than the first),
        # we choose to list the destination city.
        itinerary = []
        for day in range(1, 33):
            # Find the segment whose start is the greatest that does not exceed 'day'.
            current_city = None
            for i in range(9, -1, -1):
                if starts[i] <= day:
                    current_city = order[i]
                    break
            itinerary.append({"day": day, "city": city_names[current_city]})
        
        # For clarity print the segments as comments (optional)
        # Uncomment if you wish:
        #for seg in segments:
        #    print(f"Segment: {city_names[seg[2]]} from day {seg[0]} to day {seg[1]}")
        
        out = {"itinerary": itinerary}
        print(json.dumps(out, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()