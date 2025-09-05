from z3 import *
import json

def main():
    solver = Solver()

    # Define cities and their required stay durations.
    # Index assignment:
    # 0: Prague (5 days)
    # 1: Brussels (2 days)
    # 2: Riga (2 days)
    # 3: Munich (2 days)
    # 4: Seville (3 days)
    # 5: Stockholm (2 days)
    # 6: Istanbul (2 days)
    # 7: Amsterdam (3 days)
    # 8: Vienna (5 days)
    # 9: Split (3 days)
    cities = [
        {"name": "Prague", "duration": 5},
        {"name": "Brussels", "duration": 2},
        {"name": "Riga", "duration": 2},
        {"name": "Munich", "duration": 2},
        {"name": "Seville", "duration": 3},
        {"name": "Stockholm", "duration": 2},
        {"name": "Istanbul", "duration": 2},
        {"name": "Amsterdam", "duration": 3},
        {"name": "Vienna", "duration": 5},
        {"name": "Split", "duration": 3}
    ]
    n = len(cities)

    # For each city, we introduce:
    #   order_vars[i]: the position of city i in the itinerary (from 1 to n).
    #   start_vars[i]: the start day when you begin your stay in city i.
    order_vars = [Int(f"order_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]

    # Domain constraints:
    for i in range(n):
        solver.add(order_vars[i] >= 1, order_vars[i] <= n)
        solver.add(start_vars[i] >= 1, start_vars[i] <= 20)
    solver.add(Distinct(order_vars))

    # If a city is the first city (order==1), its start day must be 1.
    for i in range(n):
        solver.add(Implies(order_vars[i] == 1, start_vars[i] == 1))
    # If a city is the last city (order==n), its end day must be 20.
    for i in range(n):
        solver.add(Implies(order_vars[i] == n,
                           start_vars[i] + cities[i]["duration"] - 1 == 20))

    # Define allowed flights as bidirectional connections (using frozenset for unordered pairs)
    allowed_flights = set()
    def add_flight(a, b):
        allowed_flights.add(frozenset({a, b}))
    add_flight(2, 5)    # Riga and Stockholm
    add_flight(5, 1)    # Stockholm and Brussels
    add_flight(6, 3)    # Istanbul and Munich
    add_flight(6, 2)    # Istanbul and Riga
    add_flight(0, 9)    # Prague and Split
    add_flight(8, 1)    # Vienna and Brussels
    add_flight(8, 2)    # Vienna and Riga
    add_flight(9, 5)    # Split and Stockholm
    add_flight(3, 7)    # Munich and Amsterdam
    add_flight(9, 7)    # Split and Amsterdam
    add_flight(7, 5)    # Amsterdam and Stockholm
    add_flight(7, 2)    # Amsterdam and Riga
    add_flight(8, 5)    # Vienna and Stockholm
    add_flight(8, 6)    # Vienna and Istanbul
    add_flight(8, 4)    # Vienna and Seville
    add_flight(6, 7)    # Istanbul and Amsterdam
    add_flight(3, 1)    # Munich and Brussels
    add_flight(0, 3)    # Prague and Munich
    add_flight(2, 3)    # Riga and Munich (from Riga to Munich, assumed bidirectional)
    add_flight(0, 7)    # Prague and Amsterdam
    add_flight(0, 1)    # Prague and Brussels
    add_flight(0, 6)    # Prague and Istanbul
    add_flight(6, 5)    # Istanbul and Stockholm
    add_flight(8, 0)    # Vienna and Prague
    add_flight(3, 9)    # Munich and Split
    add_flight(8, 7)    # Vienna and Amsterdam
    add_flight(0, 5)    # Prague and Stockholm
    add_flight(1, 4)    # Brussels and Seville
    add_flight(3, 5)    # Munich and Stockholm
    add_flight(6, 1)    # Istanbul and Brussels
    add_flight(7, 4)    # Amsterdam and Seville
    add_flight(8, 9)    # Vienna and Split
    add_flight(3, 4)    # Munich and Seville
    add_flight(2, 1)    # Riga and Brussels
    add_flight(0, 2)    # Prague and Riga
    add_flight(8, 3)    # Vienna and Munich

    # Chain constraints: if city i is immediately before city j in the itinerary,
    # then the start day of j must equal (start day of i) + (duration of i) - 1.
    # Also, there must be a direct flight between city i and city j.
    for i in range(n):
        for j in range(n):
            if i != j:
                flight_ok = BoolVal(True) if frozenset({i, j}) in allowed_flights else BoolVal(False)
                solver.add(Implies(order_vars[i] + 1 == order_vars[j],
                                   And(start_vars[j] == start_vars[i] + cities[i]["duration"] - 1,
                                       flight_ok)))

    # Special event constraints:
    # Prague (index 0): The annual show is from Day 5 to 9 --> must be in Prague on these days.
    # With duration 5 this forces start day exactly 5.
    solver.add(start_vars[0] == 5)
    # Stockholm (index 5): Conference during Day 16 and 17 --> must start at Day 16.
    solver.add(start_vars[5] == 16)
    # Vienna (index 8): Meet friend between Day 1 and 5 --> Vienna's block must include some day in {1,...,5}.
    solver.add(start_vars[8] <= 5)
    # Riga (index 2): Meet friends between Day 15 and 16; its 2-day window must overlap {15,16}.
    # That is, either 15 or 16 is within [start, start+1].
    solver.add(Or(And(start_vars[2] <= 15, 15 <= start_vars[2] + 2 - 1),
                  And(start_vars[2] <= 16, 16 <= start_vars[2] + 2 - 1)))
    # Split (index 9): Visit relatives between Day 11 and 13; its 3-day window must overlap {11,12,13}.
    solver.add(Or(And(start_vars[9] <= 11, 11 <= start_vars[9] + 3 - 1),
                  And(start_vars[9] <= 12, 12 <= start_vars[9] + 3 - 1),
                  And(start_vars[9] <= 13, 13 <= start_vars[9] + 3 - 1)))
    
    if solver.check() == sat:
        model = solver.model()
        # Build a schedule list containing (order, start_day, end_day, city_name)
        schedule = []
        for i in range(n):
            ord_val = model.evaluate(order_vars[i]).as_long()
            start_val = model.evaluate(start_vars[i]).as_long()
            end_val = start_val + cities[i]["duration"] - 1
            schedule.append((ord_val, start_val, end_val, cities[i]["name"]))
        # Sort the schedule by order (i.e. the itinerary order)
        schedule.sort(key=lambda x: x[0])
        itinerary = []
        for ord_val, start_val, end_val, name in schedule:
            itinerary.append({"day_range": f"Day {start_val}-{end_val}", "place": name})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()