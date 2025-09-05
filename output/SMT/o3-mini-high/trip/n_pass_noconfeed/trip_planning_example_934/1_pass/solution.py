from z3 import *
import json

def main():
    # Define the cities and their required durations.
    # City indices:
    # 0: Brussels, 1: Rome, 2: Dubrovnik, 3: Geneva, 4: Budapest, 5: Riga, 6: Valencia
    city_names = ["Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"]
    durations = [5, 2, 3, 5, 2, 4, 2]  # must-visit durations for each city

    num_cities = len(city_names)
    
    # Create SMT variables:
    # order[i] is the index of the city visited in the i-th segment of the trip.
    order = [Int(f"order_{i}") for i in range(num_cities)]
    # start_day[i] is the day (in [1,17]) on which the i-th city segment starts.
    start_day = [Int(f"start_{i}") for i in range(num_cities)]
    
    s = Solver()

    # Each order element must be between 0 and num_cities-1 and all must be distinct.
    for i in range(num_cities):
        s.add(order[i] >= 0, order[i] < num_cities)
    s.add(Distinct(order))
    
    # The overall trip is 17 days.
    # We will arrange the itinerary so that if you fly from city A to B on a given day,
    # that day counts in both A and B's segments.
    #
    # With fixed durations d_i, if the itinerary order is P0, P1, ..., P6, then:
    # start_day[0] = 1, and for i>=0:
    #   start_day[i+1] = start_day[i] + (durations[P_i] - 1)
    # The end day of the last segment is: start_day[6] + durations[P6] - 1 = 17.
    s.add(start_day[0] == 1)
    for i in range(num_cities - 1):
        # Based on the city chosen for this segment, add: 
        # start_day[i+1] = start_day[i] + (duration - 1)
        s.add(start_day[i+1] == start_day[i] + Sum([If(order[i] == j, durations[j] - 1, 0) for j in range(num_cities)]))
    # Final segment's end day must be 17.
    s.add(Or([And(order[num_cities - 1] == j, start_day[num_cities - 1] + durations[j] - 1 == 17) for j in range(num_cities)]))

    # Special constraints on time windows:
    # Brussels: must be visited for 5 days and workshop must occur between day 7 and day 11.
    # That is, if Brussels is visited at segment i, then the Brussels segment [start, start+4] must intersect [7,11].
    for i in range(num_cities):
        s.add(Implies(order[i] == 0, And(start_day[i] <= 11, start_day[i] + 4 >= 7)))
        
    # Budapest: 2-day visit; meet friend between day 16 and day 17:
    for i in range(num_cities):
        s.add(Implies(order[i] == 4, And(start_day[i] <= 17, start_day[i] + 1 >= 16)))
        
    # Riga: 4-day visit; meet friends in Riga between day 4 and day 7:
    for i in range(num_cities):
        s.add(Implies(order[i] == 5, And(start_day[i] <= 7, start_day[i] + 3 >= 4)))
    
    # Define allowed direct flights between cities.
    # For two consecutive cities A (a) and B (b) in the itinerary, flight_allowed(a, b) must hold.
    def flight_allowed(a, b):
        return Or(
            # Brussels and Valencia (bidirectional)
            And(a == 0, b == 6), And(a == 6, b == 0),
            # Rome and Valencia (bidirectional)
            And(a == 1, b == 6), And(a == 6, b == 1),
            # Brussels and Geneva (bidirectional)
            And(a == 0, b == 3), And(a == 3, b == 0),
            # Rome and Geneva (bidirectional)
            And(a == 1, b == 3), And(a == 3, b == 1),
            # Dubrovnik and Geneva (bidirectional)
            And(a == 2, b == 3), And(a == 3, b == 2),
            # Valencia and Geneva (bidirectional)
            And(a == 6, b == 3), And(a == 3, b == 6),
            # From Rome to Riga (one directional: only if departing from Rome)
            And(a == 1, b == 5),
            # Geneva and Budapest (bidirectional)
            And(a == 3, b == 4), And(a == 4, b == 3),
            # Riga and Brussels (bidirectional)
            And(a == 5, b == 0), And(a == 0, b == 5),
            # Rome and Budapest (bidirectional)
            And(a == 1, b == 4), And(a == 4, b == 1),
            # Rome and Brussels (bidirectional)
            And(a == 1, b == 0), And(a == 0, b == 1),
            # Brussels and Budapest (bidirectional)
            And(a == 0, b == 4), And(a == 4, b == 0),
            # Dubrovnik and Rome (bidirectional)
            And(a == 2, b == 1), And(a == 1, b == 2)
        )
    
    for i in range(num_cities - 1):
        s.add(flight_allowed(order[i], order[i+1]))
    
    # Attempt to solve the SMT model.
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_cities):
            # Get the city index, its start day, and compute the end day based on fixed duration.
            city_index = m.evaluate(order[i]).as_long()
            start = m.evaluate(start_day[i]).as_long()
            end = start + durations[city_index] - 1
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city_names[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()