from z3 import *
import json

def main():
    solver = Solver()

    # There are 5 cities, which we number as follows:
    # 0: Stuttgart, 1: Bucharest, 2: Geneva, 3: Valencia, 4: Munich
    # Fixed durations for each city
    # Stuttgart: 2, Bucharest: 2, Geneva: 4, Valencia: 6, Munich: 7
    def duration(city):
        return If(city == 0, 2,
               If(city == 1, 2,
               If(city == 2, 4,
               If(city == 3, 6,
               7))))  # city == 4

    # Create permutation variables for the order of cities: p0, p1, p2, p3, p4.
    p = [Int(f"p{i}") for i in range(5)]
    # Create start (s) and end (e) day variables for each city visit segment.
    s = [Int(f"s{i}") for i in range(5)]
    e = [Int(f"e{i}") for i in range(5)]

    # The trip is 17 days total.
    # We model the itinerary as consecutive segments with overlap on the flight day.
    # If a city segment has duration d, then its interval is [s, e] where:
    #   e = s + d - 1.
    # For consecutive segments, the start of the next city equals the end day of the previous city.
    # This double counts the flight day as required.
    solver.add(s[0] == 1)  # trip starts on Day 1
    for i in range(5):
        # Each segment's length equals the city's planned days.
        solver.add(e[i] == s[i] + duration(p[i]) - 1)
        # Enforce that the stay lies within the overall trip days.
        solver.add(s[i] >= 1, e[i] <= 17)
    for i in range(1, 5):
        solver.add(s[i] == e[i - 1])
    # The last segment must end on day 17.
    solver.add(e[4] == 17)

    # Permutation constraints: p[0]...p[4] are a permutation of {0,1,2,3,4}
    solver.add(Distinct(p))
    for i in range(5):
        solver.add(p[i] >= 0, p[i] <= 4)

    # Define allowed direct flight pairs. The direct flights are (bidirectional):
    # Geneva <-> Munich, Munich <-> Valencia, Bucharest <-> Valencia,
    # Munich <-> Bucharest, Valencia <-> Stuttgart, Geneva <-> Valencia.
    def allowed_flight(x, y):
        return Or(
            And(x == 2, y == 4),  # Geneva -> Munich
            And(x == 4, y == 2),  # Munich -> Geneva
            And(x == 4, y == 3),  # Munich -> Valencia
            And(x == 3, y == 4),  # Valencia -> Munich
            And(x == 1, y == 3),  # Bucharest -> Valencia
            And(x == 3, y == 1),  # Valencia -> Bucharest
            And(x == 4, y == 1),  # Munich -> Bucharest
            And(x == 1, y == 4),  # Bucharest -> Munich
            And(x == 3, y == 0),  # Valencia -> Stuttgart
            And(x == 0, y == 3),  # Stuttgart -> Valencia
            And(x == 2, y == 3),  # Geneva -> Valencia
            And(x == 3, y == 2)   # Valencia -> Geneva
        )

    # For consecutive city visits, force the direct flight criteria.
    for i in range(4):
        solver.add(allowed_flight(p[i], p[i+1]))

    # Additional trip constraints:
    # 1. Visit relatives in Geneva between Day 1 and Day 4.
    #    If Geneva (city 2) is visited, then its segment must start no later than Day 4.
    for i in range(5):
        solver.add(Implies(p[i] == 2, s[i] <= 4))

    # 2. Meet friends in Munich between Day 4 and Day 10.
    #    If Munich (city 4) is visited, then its segment must start on or before Day 10.
    for i in range(5):
        solver.add(Implies(p[i] == 4, s[i] <= 10))

    # Solve for a valid itinerary.
    if solver.check() == sat:
        model = solver.model()
        # Map numeric indices to city names.
        city_names = {
            0: "Stuttgart",
            1: "Bucharest",
            2: "Geneva",
            3: "Valencia",
            4: "Munich"
        }
        itinerary = []
        for i in range(5):
            city_id = model.evaluate(p[i]).as_long()
            start_day = model.evaluate(s[i]).as_long()
            end_day = model.evaluate(e[i]).as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_id]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()