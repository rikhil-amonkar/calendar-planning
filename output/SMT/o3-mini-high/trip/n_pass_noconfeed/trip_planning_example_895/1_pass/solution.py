from z3 import *
import json

def duration_expr(x):
    # Returns the duration (number of days) for a city given its index:
    # 0: Brussels (2), 1: Venice (3), 2: London (3), 3: Lisbon (4),
    # 4: Reykjavik (3), 5: Santorini (3), 6: Madrid (5)
    return If(x == 0, 2,
           If(x == 1, 3,
           If(x == 2, 3,
           If(x == 3, 4,
           If(x == 4, 3,
           If(x == 5, 3,
           If(x == 6, 5, 0)))))))

def main():
    s = Solver()

    # City indices and names:
    # 0: Brussels, 1: Venice, 2: London, 3: Lisbon, 4: Reykjavik, 5: Santorini, 6: Madrid
    city_names = {
        0: "Brussels",
        1: "Venice",
        2: "London",
        3: "Lisbon",
        4: "Reykjavik",
        5: "Santorini",
        6: "Madrid"
    }
    
    # Define the order in which cities are visited: a permutation of 0..6.
    order = [Int(f"order_{i}") for i in range(7)]
    for i in range(7):
        s.add(order[i] >= 0, order[i] <= 6)
    s.add(Distinct(order))
    # Brussels (0) is fixed as the first city (for the conference on days 1-2)
    s.add(order[0] == 0)
    
    # Define start day for each itinerary position.
    # Each element represents the day the visit in that position starts.
    start_order = [Int(f"start_{i}") for i in range(7)]
    # The trip starts on day 1.
    s.add(start_order[0] == 1)
    
    # Enforce that when moving from one city to the next, one flies on the overlapping day.
    # If city A (with duration d_A) is visited at position i, then the next city starts on:
    # start_order[i+1] = start_order[i] + d_A - 1.
    for i in range(6):
        s.add(start_order[i+1] == start_order[i] + duration_expr(order[i]) - 1)
    # The overall trip spans 17 days:
    s.add(start_order[6] + duration_expr(order[6]) - 1 == 17)
    
    # Create individual start time variables for each city.
    st = [Int(f"st_{c}") for c in range(7)]
    # Link each city's start time to the itinerary position at which it is visited.
    for pos in range(7):
        for c in range(7):
            s.add(Implies(order[pos] == c, st[c] == start_order[pos]))
    
    # Add city-specific constraints:
    # Venice (index 1): 3-day visit and must meet relatives between day 5 and day 7.
    # This constraint is satisfied if the Venice visit [st1, st1+2] overlaps with days 5-7.
    s.add(st[1] <= 7)
    s.add(st[1] + 2 >= 5)
    
    # Madrid (index 6): 5-day visit and the wedding must occur between day 7 and day 11.
    # So the Madrid visit [st6, st6+4] must cover at least one day in 7-11.
    s.add(st[6] <= 11)
    s.add(st[6] + 4 >= 7)
    
    # The conference in Brussels (index 0) on days 1 and 2 is automatically covered since Brussels is first:
    # Brussels segment: [st0, st0+1] = [1,2].

    # Allowed direct flights between cities for consecutive legs:
    # Each transition from city A (at position i) to city B (at position i+1)
    # must be in one of the following allowed pairs.
    allowed = [
        (0, 1), (1, 0),          # Brussels and Venice
        (0, 2), (2, 0),          # Brussels and London
        (0, 3), (3, 0),          # Brussels and Lisbon
        (0, 4), (4, 0),          # Brussels and Reykjavik
        (0, 6), (6, 0),          # Brussels and Madrid
        (1, 6), (6, 1),          # Venice and Madrid
        (1, 5), (5, 1),          # Venice and Santorini
        (3, 4), (4, 3),          # Lisbon and Reykjavik
        (3, 1), (1, 3),          # Lisbon and Venice
        (4, 6),                 # from Reykjavik to Madrid (directed)
        (6, 2), (2, 6),          # Madrid and London
        (5, 2), (2, 5),          # Santorini and London
        (2, 4), (4, 2),          # London and Reykjavik
        (3, 2), (2, 3),          # Lisbon and London
        (3, 6), (6, 3),          # Lisbon and Madrid
        (6, 5), (5, 6),          # Madrid and Santorini
        (1, 2), (2, 1)           # Venice and London
    ]
    
    # For each consecutive pair in the itinerary, ensure there is an allowed direct flight.
    for i in range(6):
        trans_conditions = []
        for (u, v) in allowed:
            trans_conditions.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(trans_conditions))
    
    # Solve the SMT model.
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for pos in range(7):
            city_idx = m.evaluate(order[pos]).as_long()
            city_name = city_names[city_idx]
            start_day = m.evaluate(start_order[pos]).as_long()
            # Determine duration based on city.
            if city_idx == 0:
                dur = 2
            elif city_idx == 1:
                dur = 3
            elif city_idx == 2:
                dur = 3
            elif city_idx == 3:
                dur = 4
            elif city_idx == 4:
                dur = 3
            elif city_idx == 5:
                dur = 3
            elif city_idx == 6:
                dur = 5
            end_day = start_day + dur - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_name})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()