from z3 import *
import json

def main():
    s = Solver()

    # Define the list of cities and their required durations
    cities = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]
    # Durations: Reykjavik:4, Riga:2, Oslo:3, Lyon:5, Dubrovnik:2, Madrid:2, Warsaw:4, London:3
    # Index mapping: 0:Reykjavik, 1:Riga, 2:Oslo, 3:Lyon, 4:Dubrovnik, 5:Madrid, 6:Warsaw, 7:London

    # Define allowed direct flights.
    # For pairs described as "CityA and CityB", we add them bidirectionally.
    # For "from Reykjavik to Madrid", we add only the directed edge.
    allowed_flights = []
    
    def add_bidirectional(a, b):
        allowed_flights.append((a, b))
        allowed_flights.append((b, a))
    
    # Warsaw and Reykjavik
    add_bidirectional(6, 0)
    # Oslo and Madrid
    add_bidirectional(2, 5)
    # Warsaw and Riga
    add_bidirectional(6, 1)
    # Lyon and London
    add_bidirectional(3, 7)
    # Madrid and London
    add_bidirectional(5, 7)
    # Warsaw and London
    add_bidirectional(6, 7)
    # from Reykjavik to Madrid (directed)
    allowed_flights.append((0, 5))
    # Warsaw and Oslo
    add_bidirectional(6, 2)
    # Oslo and Dubrovnik
    add_bidirectional(2, 4)
    # Oslo and Reykjavik
    add_bidirectional(2, 0)
    # Riga and Oslo
    add_bidirectional(1, 2)
    # Oslo and Lyon
    add_bidirectional(2, 3)
    # Oslo and London
    add_bidirectional(2, 7)
    # London and Reykjavik
    add_bidirectional(7, 0)
    # Warsaw and Madrid
    add_bidirectional(6, 5)
    # Madrid and Lyon
    add_bidirectional(5, 3)
    # Dubrovnik and Madrid
    add_bidirectional(4, 5)

    n = 8  # number of cities/segments
    # Create SMT integer variables for city index, start day and end day for each itinerary segment
    city_vars = [Int("city_%d" % i) for i in range(n)]
    start_vars = [Int("start_%d" % i) for i in range(n)]
    end_vars = [Int("end_%d" % i) for i in range(n)]

    # Domain constraints: each city variable is between 0 and 7, start and end days between 1 and 18.
    for i in range(n):
        s.add(city_vars[i] >= 0, city_vars[i] < 8)
        s.add(start_vars[i] >= 1, start_vars[i] <= 18)
        s.add(end_vars[i] >= 1, end_vars[i] <= 18)
    
    # All cities must be visited exactly once.
    s.add(Distinct(city_vars))

    # The itinerary spans exactly 18 days: the first day is Day 1 and the last day is Day 18.
    s.add(start_vars[0] == 1)
    s.add(end_vars[n-1] == 18)

    # For each itinerary segment, the duration must equal the required days for that city.
    for i in range(n):
        duration_expr = If(city_vars[i] == 0, 4,
                         If(city_vars[i] == 1, 2,
                         If(city_vars[i] == 2, 3,
                         If(city_vars[i] == 3, 5,
                         If(city_vars[i] == 4, 2,
                         If(city_vars[i] == 5, 2,
                         If(city_vars[i] == 6, 4,
                         If(city_vars[i] == 7, 3, 0))))))))
        s.add(end_vars[i] == start_vars[i] + duration_expr - 1)

    # Transition constraints:
    # If you fly from city A to city B on day X, then day X is counted in both segments.
    # Thus, for every consecutive segments, the start day of the next equals the end day of the previous.
    for i in range(n - 1):
        s.add(start_vars[i + 1] == end_vars[i])

    # Flight constraints: For every consecutive pair of cities, a direct flight must exist.
    for i in range(n - 1):
        valid_connection = []
        for (src, dst) in allowed_flights:
            valid_connection.append(And(city_vars[i] == src, city_vars[i + 1] == dst))
        s.add(Or(valid_connection))

    # Special event constraints:
    # Friend meeting in Riga (city index 1) must happen between day 4 and day 5 (i.e. either day 4 or 5 is within the visit).
    for i in range(n):
        s.add(Implies(city_vars[i] == 1,
                      Or(And(start_vars[i] <= 4, 4 <= end_vars[i]),
                         And(start_vars[i] <= 5, 5 <= end_vars[i]))))
    
    # Wedding in Dubrovnik (city index 4) must occur between day 7 and day 8.
    for i in range(n):
        s.add(Implies(city_vars[i] == 4,
                      Or(And(start_vars[i] <= 7, 7 <= end_vars[i]),
                         And(start_vars[i] <= 8, 8 <= end_vars[i]))))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            city_index = m.evaluate(city_vars[i]).as_long()
            start_day = m.evaluate(start_vars[i]).as_long()
            end_day = m.evaluate(end_vars[i]).as_long()
            itinerary.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": cities[city_index]
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()