#!/usr/bin/env python3
from z3 import *
import json

def main():
    solver = Solver()

    # Define cities with their indices and durations.
    # Index mapping:
    # 0: Prague (duration 3, workshop between day 1-3)
    # 1: Warsaw (duration 4, meet friends between day 20-23)
    # 2: Dublin (duration 3)
    # 3: Athens (duration 3)
    # 4: Vilnius (duration 4)
    # 5: Porto (duration 5, conference between day 16-20)
    # 6: London (duration 3, wedding between day 3-5)
    # 7: Seville (duration 2)
    # 8: Lisbon (duration 5, relatives between day 5-9)
    # 9: Dubrovnik (duration 3)
    cities = ["Prague", "Warsaw", "Dublin", "Athens", "Vilnius", "Porto", "London", "Seville", "Lisbon", "Dubrovnik"]
    durations = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]

    num_slots = 10  # 10 cities in the itinerary

    # Decision variables:
    # itinerary[i] is the city index (0..9) visited in slot i.
    itinerary = [Int(f"itinerary_{i}") for i in range(num_slots)]
    # start_days[i] is the starting day (in the overall 26-day period) when city in slot i is visited.
    start_days = [Int(f"s_{i}") for i in range(num_slots)]

    # Each itinerary slot must be a valid city index.
    for i in range(num_slots):
        solver.add(And(itinerary[i] >= 0, itinerary[i] < 10))
    # All cities must be visited exactly once.
    solver.add(Distinct(itinerary))

    # Helper functions to return duration and transition delta.
    def dur(city):
        return If(city == 0, 3,
               If(city == 1, 4,
               If(city == 2, 3,
               If(city == 3, 3,
               If(city == 4, 4,
               If(city == 5, 5,
               If(city == 6, 3,
               If(city == 7, 2,
               If(city == 8, 5, 3)))))))))

    # delta(city) = duration(city) - 1.
    def delta(city):
        return dur(city) - 1

    # Set the starting day for the first slot.
    solver.add(start_days[0] == 1)
    # For each subsequent slot, the start day equals the previous slot's start day plus (duration - 1).
    for i in range(1, num_slots):
        solver.add(start_days[i] == start_days[i-1] + delta(itinerary[i-1]))

    # The end day of the last city must equal day 26.
    # End day for slot i is start_days[i] + (duration - 1)
    solver.add(start_days[num_slots-1] + dur(itinerary[num_slots-1]) - 1 == 26)

    # Define allowed direct flight connections.
    # The flights are bidirectional. The given direct flight pairs (converted to indices) are:
    # Warsaw-Vilnius (1,4), Prague-Athens (0,3), London-Lisbon (6,8),
    # Lisbon-Porto (8,5), Prague-Lisbon (0,8), London-Dublin (6,2),
    # Athens-Vilnius (3,4), Athens-Dublin (3,2), Prague-London (0,6),
    # London-Warsaw (6,1), Dublin-Seville (2,7), Seville-Porto (7,5),
    # Lisbon-Athens (8,3), Dublin-Porto (2,5), Athens-Warsaw (3,1),
    # Lisbon-Warsaw (8,1), Porto-Warsaw (5,1), Prague-Warsaw (0,1),
    # Prague-Dublin (0,2), Athens-Dubrovnik (3,9), Lisbon-Dublin (8,2),
    # Dubrovnik-Dublin (9,2), Lisbon-Seville (8,7), London-Athens (6,3)
    allowed_pairs = [
        (0, 3), (1, 4), (6, 8), (8, 5), (0, 8), (6, 2), (3, 4),
        (3, 2), (0, 6), (6, 1), (2, 7), (7, 5), (8, 3), (2, 5),
        (3, 1), (8, 1), (5, 1), (0, 1), (0, 2), (3, 9), (8, 2),
        (9, 2), (8, 7), (6, 3)
    ]
    # Helper function for allowed flight between two cities.
    def allowed_flight(a, b):
        conds = []
        for (p, q) in allowed_pairs:
            conds.append(And(a == p, b == q))
            conds.append(And(a == q, b == p))
        return Or(conds)

    # Enforce that consecutive cities in the itinerary must have a direct flight connection.
    for i in range(num_slots - 1):
        solver.add(allowed_flight(itinerary[i], itinerary[i+1]))

    # Add event constraints.
    # For each slot, if a city with an event is visited then the visit's day range must include the event window.
    for i in range(num_slots):
        # Prague (index 0): workshop between day 1 and day 3.
        solver.add(Implies(itinerary[i] == 0, start_days[i] <= 3))
        # Warsaw (index 1): meet friends between day 20 and day 23.
        # For a 4-day visit, [s, s+3] must intersect [20,23]:
        #   s <= 23 and s+3 >= 20  --> s >= 17.
        solver.add(Implies(itinerary[i] == 1, And(start_days[i] <= 23, start_days[i] >= 17)))
        # London (index 6): wedding between day 3 and day 5.
        solver.add(Implies(itinerary[i] == 6, start_days[i] <= 5))
        # Lisbon (index 8): relatives between day 5 and day 9.
        solver.add(Implies(itinerary[i] == 8, start_days[i] <= 9))
        # Porto (index 5): conference between day 16 and day 20.
        # For a 5-day visit, [s, s+4] must intersect [16,20]:
        #   s <= 20 and s+4 >= 16  --> s >= 12.
        solver.add(Implies(itinerary[i] == 5, And(start_days[i] <= 20, start_days[i] >= 12)))

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary_list = []
        for i in range(num_slots):
            city_index = model.evaluate(itinerary[i]).as_long()
            start_day = model.evaluate(start_days[i]).as_long()
            end_day = start_day + durations[city_index] - 1
            itinerary_list.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()