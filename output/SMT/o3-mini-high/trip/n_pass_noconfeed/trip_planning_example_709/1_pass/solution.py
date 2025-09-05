from z3 import *
import json

def main():
    s = Solver()
    
    n_cities = 6
    # City codes:
    # 0: Helsinki (4 days)
    # 1: Valencia (5 days)
    # 2: Dubrovnik (4 days)
    # 3: Porto (3 days)
    # 4: Prague (3 days)
    # 5: Reykjavik (4 days)
    city_names = {0: "Helsinki", 1: "Valencia", 2: "Dubrovnik", 3: "Porto", 4: "Prague", 5: "Reykjavik"}
    
    # durations for each city code
    def duration(city):
        return If(city == 0, 4,
               If(city == 1, 5,
               If(city == 2, 4,
               If(city == 3, 3,
               If(city == 4, 3,
               If(city == 5, 4, 0))))))
    
    # Create variables for the itinerary order and start day for each segment.
    cities = [Int(f"city_{i}") for i in range(n_cities)]
    starts = [Int(f"start_{i}") for i in range(n_cities)]
    
    # Each city variable must be between 0 and 5.
    for c in cities:
        s.add(And(c >= 0, c < n_cities))
    # All cities must be visited exactly once.
    s.add(Distinct(cities))
    
    # The trip lasts 18 days. The first day is day 1.
    s.add(starts[0] == 1)
    
    # Define flight connection constraint function.
    # Allowed direct flights (bidirectional):
    # Helsinki <-> Prague, Prague <-> Valencia, Valencia <-> Porto, Helsinki <-> Reykjavik,
    # Dubrovnik <-> Helsinki, Reykjavik <-> Prague.
    def allowed_flight(c1, c2):
        return Or(
            And(c1 == 0, c2 == 4), And(c1 == 4, c2 == 0),       # Helsinki <-> Prague
            And(c1 == 4, c2 == 1), And(c1 == 1, c2 == 4),       # Prague <-> Valencia
            And(c1 == 1, c2 == 3), And(c1 == 3, c2 == 1),       # Valencia <-> Porto
            And(c1 == 0, c2 == 5), And(c1 == 5, c2 == 0),       # Helsinki <-> Reykjavik
            And(c1 == 2, c2 == 0), And(c1 == 0, c2 == 2),       # Dubrovnik <-> Helsinki
            And(c1 == 5, c2 == 4), And(c1 == 4, c2 == 5)        # Reykjavik <-> Prague
        )
    
    # Add constraints for consecutive cities: direct flights must exist
    for i in range(n_cities - 1):
        s.add(allowed_flight(cities[i], cities[i+1]))
    
    # Flight day overlapping constraint:
    # If you fly from city A to city B on a transition day X,
    # then the last day of A's stay is the first day of B's stay.
    # For each segment, (start_day + duration - 1) of current city equals start day of next city.
    for i in range(n_cities - 1):
        s.add(starts[i+1] == starts[i] + duration(cities[i]) - 1)
    
    # Total trip constraint: The last city's end day must be day 18.
    s.add(starts[n_cities - 1] + duration(cities[n_cities - 1]) - 1 == 18)
    
    # Constraint: If Porto (code 3) is visited, then during its 3-day stay one of the days must be between day 16 and day 18.
    for i in range(n_cities):
        # For Porto, duration is 3 so the end day is starts[i] + 2.
        port_meet = Or(
            And(starts[i] <= 16, starts[i] + 2 >= 16),
            And(starts[i] <= 17, starts[i] + 2 >= 17),
            And(starts[i] <= 18, starts[i] + 2 >= 18)
        )
        s.add(Implies(cities[i] == 3, port_meet))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_cities):
            city_code = m[cities[i]].as_long()
            start_day = m[starts[i]].as_long()
            # Determine fixed duration for the city
            if city_code == 0:
                dur = 4
            elif city_code == 1:
                dur = 5
            elif city_code == 2:
                dur = 4
            elif city_code == 3:
                dur = 3
            elif city_code == 4:
                dur = 3
            elif city_code == 5:
                dur = 4
            else:
                dur = 0
            end_day = start_day + dur - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_names[city_code]})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()