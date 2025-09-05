from z3 import *
import json

def main():
    s = Solver()

    # Cities: 0=Prague, 1=Berlin, 2=Tallinn, 3=Stockholm
    cities = [Int(f"city_{i}") for i in range(4)]
    for city in cities:
        s.add(Or(city == 0, city == 1, city == 2, city == 3))
    s.add(Distinct(cities))

    # Duration for each segment based on the city
    durations = [Int(f"d_{i}") for i in range(4)]
    for i in range(4):
        s.add(durations[i] == If(cities[i] == 0, 2,     # Prague: 2 days
                           If(cities[i] == 1, 3,         # Berlin: 3 days
                           If(cities[i] == 2, 5,         # Tallinn: 5 days
                                                  5))))   # Stockholm: 5 days

    # Start times for segments.
    t = [Int(f"t_{i}") for i in range(4)]
    s.add(t[0] == 1)  # Trip starts on Day 1
    s.add(t[1] == t[0] + durations[0] - 1)  # Overlap flight: last day of segment 0 == first day of segment 1
    s.add(t[2] == t[1] + durations[1] - 1)
    s.add(t[3] == t[2] + durations[2] - 1)
    # The end of segment 3 must be Day 12
    s.add(t[3] + durations[3] - 1 == 12)

    # Allowed direct flight pairs (order matters because you only take direct flights)
    # Allowed pairs: (Prague,Tallinn), (Tallinn,Prague),
    # (Stockholm,Tallinn), (Tallinn,Stockholm),
    # (Prague,Stockholm), (Stockholm,Prague),
    # (Stockholm,Berlin), (Berlin,Stockholm),
    # (Berlin,Tallinn), (Tallinn,Berlin)
    def allowed_pair(a, b):
        return Or(
            And(a == 0, b == 2),
            And(a == 2, b == 0),
            And(a == 3, b == 2),
            And(a == 2, b == 3),
            And(a == 0, b == 3),
            And(a == 3, b == 0),
            And(a == 3, b == 1),
            And(a == 1, b == 3),
            And(a == 1, b == 2),
            And(a == 2, b == 1)
        )
    s.add(allowed_pair(cities[0], cities[1]))
    s.add(allowed_pair(cities[1], cities[2]))
    s.add(allowed_pair(cities[2], cities[3]))

    # Conference constraints: Must be in Berlin (city == 1) on days 6 and 8.
    conf_days = [6, 8]
    for conf_day in conf_days:
        in_berlin = []
        for i in range(4):
            # A segment covers day d if: t[i] <= d <= t[i] + durations[i] - 1.
            in_berlin.append(And(t[i] <= conf_day, conf_day <= t[i] + durations[i] - 1, cities[i] == 1))
        s.add(Or(in_berlin))

    # Relatives constraint: If visiting Tallinn (city==2), the stay must overlap with days 8 to 12.
    for i in range(4):
        s.add(Implies(cities[i] == 2, And(t[i] <= 12, t[i] + durations[i] - 1 >= 8)))

    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        # Map integers to city names
        city_names = {0: "Prague", 1: "Berlin", 2: "Tallinn", 3: "Stockholm"}
        itinerary = []
        for i in range(4):
            start_day = m[t[i]].as_long()
            dur = m[durations[i]].as_long()
            end_day = start_day + dur - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[m[cities[i]].as_long()]
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()