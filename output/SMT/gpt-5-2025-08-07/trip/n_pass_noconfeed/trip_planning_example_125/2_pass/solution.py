import json
from z3 import Solver, Ints, Int, If, Or, And, Distinct, sat

def main():
    # Parameters (trip constraints as input variables)
    total_days = 15
    cities = {
        "Manchester": 0,
        "Stuttgart": 1,
        "Seville": 2,
    }
    city_names = {v: k for k, v in cities.items()}

    # Desired stay durations per city (these include travel-day overlaps)
    desired_days = {
        cities["Manchester"]: 4,
        cities["Stuttgart"]: 6,
        cities["Seville"]: 7,
    }

    # Direct flight pairs (undirected)
    direct_pairs = {
        (cities["Manchester"], cities["Seville"]),
        (cities["Seville"], cities["Manchester"]),
        (cities["Stuttgart"], cities["Manchester"]),
        (cities["Manchester"], cities["Stuttgart"]),
    }

    # Friend meeting in Stuttgart window
    meet_city = cities["Stuttgart"]
    meet_window_start = 1
    meet_window_end = 6

    # SMT variables
    c1, c2, c3 = Ints('c1 c2 c3')               # city sequence (3 segments)
    l1, l2, l3 = Ints('l1 l2 l3')               # durations for each segment

    s = Solver()

    # Domain constraints: each segment is one of the 3 cities
    domain = [
        Or(c1 == cities["Manchester"], c1 == cities["Stuttgart"], c1 == cities["Seville"]),
        Or(c2 == cities["Manchester"], c2 == cities["Stuttgart"], c2 == cities["Seville"]),
        Or(c3 == cities["Manchester"], c3 == cities["Stuttgart"], c3 == cities["Seville"])
    ]
    s.add(domain)

    # All three cities must be distinct (exactly 3 cities visited)
    s.add(Distinct(c1, c2, c3))

    # Map segment lengths to desired durations based on the chosen city
    def len_for_city(ci):
        return If(ci == cities["Manchester"], desired_days[cities["Manchester"]],
                  If(ci == cities["Stuttgart"], desired_days[cities["Stuttgart"]],
                     desired_days[cities["Seville"]]))
    s.add(l1 == len_for_city(c1))
    s.add(l2 == len_for_city(c2))
    s.add(l3 == len_for_city(c3))

    # Lengths must be positive
    s.add(l1 >= 1, l2 >= 1, l3 >= 1)

    # Travel between segments must be direct flights
    def direct(a, b):
        return Or(*[And(a == x, b == y) for (x, y) in direct_pairs])
    s.add(direct(c1, c2))
    s.add(direct(c2, c3))

    # With 3 segments and travel-day overlap counted in both cities:
    # unique trip days = l1 + l2 + l3 - (number_of_flights)
    # number_of_flights = 2
    s.add(l1 + l2 + l3 == total_days + 2)

    # Segment day ranges (overlapping on travel days)
    start1 = Int('start1')
    end1 = Int('end1')
    start2 = Int('start2')
    end2 = Int('end2')
    start3 = Int('start3')
    end3 = Int('end3')
    s.add(start1 == 1)
    s.add(end1 == l1)
    s.add(start2 == l1)
    s.add(end2 == l1 + l2 - 1)
    s.add(start3 == l1 + l2 - 1)
    s.add(end3 == l1 + l2 + l3 - 2)
    s.add(end3 == total_days)

    # Meet friend in Stuttgart between day 1 and day 6
    meet_cond = Or(
        And(c1 == meet_city, start1 <= meet_window_end, end1 >= meet_window_start),
        And(c2 == meet_city, start2 <= meet_window_end, end2 >= meet_window_start),
        And(c3 == meet_city, start3 <= meet_window_end, end3 >= meet_window_start),
    )
    s.add(meet_cond)

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Extract values
    c1v = m.evaluate(c1).as_long()
    c2v = m.evaluate(c2).as_long()
    c3v = m.evaluate(c3).as_long()
    l1v = m.evaluate(l1).as_long()
    l2v = m.evaluate(l2).as_long()
    l3v = m.evaluate(l3).as_long()

    # Compute day ranges following the overlap rules
    segs = []
    segs.append((1, l1v, c1v))                              # [1 .. l1]
    segs.append((l1v, l1v + l2v - 1, c2v))                  # [l1 .. l1+l2-1]
    segs.append((l1v + l2v - 1, total_days, c3v))           # [l1+l2-1 .. total_days]

    itinerary = []
    for (start, end, city_code) in segs:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city_names[city_code]
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()