from z3 import *
import json

# Mapping of city IDs to names and their required durations.
# City IDs: 0: Frankfurt (3 days), 1: Naples (4 days), 2: Helsinki (4 days), 3: Lyon (3 days), 4: Prague (2 days)
id_to_city = {0: "Frankfurt", 1: "Naples", 2: "Helsinki", 3: "Lyon", 4: "Prague"}
durations_dict = {"Frankfurt": 3, "Naples": 4, "Helsinki": 4, "Lyon": 3, "Prague": 2}

def city_duration(city):
    # city is a Z3 integer expression; return the duration depending on its value.
    return If(city == 0, 3,
           If(city == 1, 4,
           If(city == 2, 4,
           If(city == 3, 3,
           If(city == 4, 2, 0)))))

def main():
    s = Solver()

    # Create 5 integer decision variables for the order in which the cities are visited.
    order = [Int("order%d" % i) for i in range(5)]
    
    # Create 5 integer variables for the start day of each city segment.
    # When flying from city A to city B on a flight day, that day (the start day of B)
    # equals the end day of A, so it counts in both.
    start = [Int("start%d" % i) for i in range(5)]

    # Domain constraints: each order variable must be between 0 and 4.
    for i in range(5):
        s.add(And(order[i] >= 0, order[i] <= 4))
    
    # Each city is visited exactly once.
    s.add(Distinct(order))
    
    # Anchor: the trip starts on day 1.
    s.add(start[0] == 1)
    
    # Chain constraints: if you are in a city for its required days,
    # then the next city starts on the flight day (which is the last day of the current stay).
    # That is, for position i, the end day = start[i] + duration - 1,
    # and then start[i+1] equals that same day.
    for i in range(4):
        s.add(start[i+1] == start[i] + city_duration(order[i]) - 1)
        
    # Overall trip: the final city ends on day 12.
    s.add(start[4] + city_duration(order[4]) - 1 == 12)
    
    # Allowed direct flights between consecutive cities.
    # Given flights (bidirectional):
    #   Prague <-> Lyon, Prague <-> Frankfurt, Frankfurt <-> Lyon,
    #   Helsinki <-> Naples, Helsinki <-> Frankfurt, Naples <-> Frankfurt,
    #   Prague <-> Helsinki.
    allowed_pairs = [
        (4, 3), (3, 4),     # Prague and Lyon
        (4, 0), (0, 4),     # Prague and Frankfurt
        (0, 3), (3, 0),     # Frankfurt and Lyon
        (2, 1), (1, 2),     # Helsinki and Naples
        (2, 0), (0, 2),     # Helsinki and Frankfurt
        (1, 0), (0, 1),     # Naples and Frankfurt
        (4, 2), (2, 4)      # Prague and Helsinki
    ]
    for i in range(4):
        # For each consecutive pair, one of the allowed flight pairs must hold.
        flight_options = []
        for (a, b) in allowed_pairs:
            flight_options.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(flight_options))
    
    # Event constraints:
    # 1. Helsinki (city id 2) must cover days 2 to 5.
    # Since Helsinki requires 4 days, the only way to cover days 2,3,4,5 is to start exactly on day 2.
    for i in range(5):
        s.add(Implies(order[i] == 2, start[i] == 2))
    
    # 2. A workshop in Prague (city id 4) must be attended between day 1 and day 2.
    # Prague is a 2‑day visit; so if visited, its start must be either day 1 or day 2.
    for i in range(5):
        s.add(Implies(order[i] == 4, start[i] <= 2))
    
    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(5):
            city_id = m.evaluate(order[i]).as_long()
            city_name = id_to_city[city_id]
            seg_start = m.evaluate(start[i]).as_long()
            seg_duration = durations_dict[city_name]
            seg_end = seg_start + seg_duration - 1
            itinerary.append({
                "day_range": "Day {}-{}".format(seg_start, seg_end),
                "place": city_name
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()