from z3 import *

def main():
    cities = ["Milan", "Naples", "Seville"]
    n = 12  # total days

    s = Solver()

    # a_i for days 1 to 13 (a_1 to a_13)
    a = [Int('a_%d' % i) for i in range(1, n+2)]
    # flight_i for days 1 to 12
    flight = [Bool('flight_%d' % i) for i in range(1, n+1)]
    # to_i for flights on days 1 to 12
    to = [Int('to_%d' % i) for i in range(1, n+1)]

    # All a_i and to_i must be in {0,1,2}
    for i in range(len(a)):
        s.add(a[i] >= 0, a[i] <= 2)
    for i in range(len(to)):
        s.add(to[i] >= 0, to[i] <= 2)

    # Flight constraints: if flight on day i, then a[i] != to[i] and valid flight pair, and a[i+1] = to[i]
    for i in range(n):
        s.add(If(flight[i],
                 And(
                     a[i] != to[i],
                     Or(
                         And(a[i] == 0, to[i] == 2),
                         And(a[i] == 2, to[i] == 0),
                         And(a[i] == 0, to[i] == 1),
                         And(a[i] == 1, to[i] == 0)
                     ),
                     a[i+1] == to[i]
                 ),
                 a[i+1] == a[i]
               ))

    # Exactly 2 flight days
    s.add(Sum([If(flight[i], 1, 0) for i in range(n)]) == 2)

    # Count days per city (including flight days)
    milan_days = 0
    naples_days = 0
    seville_days = 0
    for i in range(n):
        milan_days += If(Or(a[i] == 0, And(flight[i], to[i] == 0)), 1, 0)
        naples_days += If(Or(a[i] == 1, And(flight[i], to[i] == 1)), 1, 0)
        seville_days += If(Or(a[i] == 2, And(flight[i], to[i] == 2)), 1, 0)
    s.add(milan_days == 7, naples_days == 3, seville_days == 4)

    # Must be in Seville on days 9,10,11,12 (0-indexed days 8,9,10,11)
    for i in [8,9,10,11]:
        s.add(Or(
            And(flight[i] == False, a[i] == 2),
            And(flight[i] == True, Or(a[i] == 2, to[i] == 2))
        ))

    if s.check() == sat:
        m = s.model()
        a_vals = [m.evaluate(a_i) for a_i in a]
        flight_vals = [m.evaluate(flight_i) for flight_i in flight]
        to_vals = [m.evaluate(to_i) for to_i in to]

        # Identify flight days (days 1-12 where flight is True)
        flight_days = []
        for i in range(n):
            if is_true(flight_vals[i]):
                flight_days.append(i+1)  # convert 0-indexed to day number
        flight_days.sort()

        itinerary = []

        # Segment 1: from day 1 to first flight day
        start1 = 1
        end1 = flight_days[0]
        city1_index = a_vals[0].as_long()
        city1_str = cities[city1_index]
        itinerary.append({"day_range": "Day %d-%d" % (start1, end1), "place": city1_str})
        itinerary.append({"day_range": "Day %d" % end1, "place": city1_str})
        to_city1_index = to_vals[flight_days[0]-1].as_long()
        to_city1_str = cities[to_city1_index]
        itinerary.append({"day_range": "Day %d" % end1, "place": to_city1_str})

        # Segment 2: from first flight day to second flight day
        start2 = flight_days[0]
        end2 = flight_days[1]
        itinerary.append({"day_range": "Day %d-%d" % (start2, end2), "place": to_city1_str})
        itinerary.append({"day_range": "Day %d" % end2, "place": to_city1_str})
        to_city2_index = to_vals[flight_days[1]-1].as_long()
        to_city2_str = cities[to_city2_index]
        itinerary.append({"day_range": "Day %d" % end2, "place": to_city2_str})

        # Segment 3: from second flight day to day 12
        start3 = flight_days[1]
        end3 = n
        itinerary.append({"day_range": "Day %d-%d" % (start3, end3), "place": to_city2_str})

        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()