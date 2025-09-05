from z3 import *
import json

def main():
    # Define City as an EnumSort with the 8 cities.
    City, (Mykonos, Krakow, Vilnius, Helsinki, Dubrovnik, Oslo, Madrid, Paris) = EnumSort("City", 
        ["Mykonos", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Oslo", "Madrid", "Paris"])
    
    # Function to return the duration for each city.
    def duration(city):
        return If(city == Mykonos, 4,
               If(city == Krakow, 5,
               If(city == Vilnius, 2,
               If(city == Helsinki, 2,
               If(city == Dubrovnik, 3,
               If(city == Oslo, 2,
               If(city == Madrid, 5,
               If(city == Paris, 2, 0))))))))
    
    # Function to enforce allowed flight connections.
    # Note: All pairs are treated bidirectionally except the Krakow->Vilnius flight which is one directional.
    def allowed_flight(c1, c2):
        return Or(
            And(c1 == Oslo, c2 == Krakow), And(c1 == Krakow, c2 == Oslo),
            And(c1 == Oslo, c2 == Paris), And(c1 == Paris, c2 == Oslo),
            And(c1 == Paris, c2 == Madrid), And(c1 == Madrid, c2 == Paris),
            And(c1 == Helsinki, c2 == Vilnius), And(c1 == Vilnius, c2 == Helsinki),
            And(c1 == Oslo, c2 == Madrid), And(c1 == Madrid, c2 == Oslo),
            And(c1 == Oslo, c2 == Helsinki), And(c1 == Helsinki, c2 == Oslo),
            And(c1 == Helsinki, c2 == Krakow), And(c1 == Krakow, c2 == Helsinki),
            And(c1 == Dubrovnik, c2 == Helsinki), And(c1 == Helsinki, c2 == Dubrovnik),
            And(c1 == Dubrovnik, c2 == Madrid), And(c1 == Madrid, c2 == Dubrovnik),
            And(c1 == Oslo, c2 == Dubrovnik), And(c1 == Dubrovnik, c2 == Oslo),
            And(c1 == Krakow, c2 == Paris), And(c1 == Paris, c2 == Krakow),
            And(c1 == Madrid, c2 == Mykonos), And(c1 == Mykonos, c2 == Madrid),
            And(c1 == Oslo, c2 == Vilnius), And(c1 == Vilnius, c2 == Oslo),
            And(c1 == Krakow, c2 == Vilnius),  # only allowed in this direction
            And(c1 == Helsinki, c2 == Paris), And(c1 == Paris, c2 == Helsinki),
            And(c1 == Vilnius, c2 == Paris), And(c1 == Paris, c2 == Vilnius),
            And(c1 == Helsinki, c2 == Madrid), And(c1 == Madrid, c2 == Helsinki)
        )
    
    solver = Solver()
    
    # There are 8 segments corresponding to the 8 cities in the itinerary.
    num_segments = 8
    cities_vars = [Const(f"city_{i}", City) for i in range(num_segments)]
    start_vars = [Int(f"start_{i}") for i in range(num_segments)]
    
    # Enforce that each city is visited exactly once.
    solver.add(Distinct(cities_vars))
    
    # The itinerary starts at Day 1.
    solver.add(start_vars[0] == 1)
    
    # Transition constraints: if you fly on day X, you are in both cities on day X.
    # For segment i, end_day = start_day + duration - 1.
    # And for i>=1, start[i] = end[i-1].
    for i in range(num_segments - 1):
        solver.add(start_vars[i+1] == start_vars[i] + duration(cities_vars[i]) - 1)
    
    # The end of the last segment must be Day 18.
    solver.add(start_vars[num_segments - 1] + duration(cities_vars[num_segments - 1]) - 1 == 18)
    
    # Special city constraints:
    # 1. Mykonos must be visited for 4 days between Day 15 and Day 18.
    #    This forces the Mykonos segment to start on Day 15.
    for i in range(num_segments):
        solver.add(Implies(cities_vars[i] == Mykonos, start_vars[i] == 15))
    
    # 2. Dubrovnik: You must attend a show from Day 2 to Day 4.
    #    With a 3-day stay, the only way to cover Days 2-4 is to start on Day 2.
    for i in range(num_segments):
        solver.add(Implies(cities_vars[i] == Dubrovnik, start_vars[i] == 2))
    
    # 3. Oslo: Meet your friends between Day 1 and Day 2.
    #    If Oslo is visited, then its start day must be Day 1 or Day 2.
    for i in range(num_segments):
        solver.add(Implies(cities_vars[i] == Oslo, start_vars[i] <= 2))
    
    # Additional ordering considerations:
    # Since Mykonos must span Days 15-18 and its duration is 4 days, it must be the last segment.
    solver.add(cities_vars[num_segments - 1] == Mykonos)
    # Dubrovnik cannot be the first city because that would force start day 1 but it needs to start at Day 2.
    solver.add(cities_vars[0] != Dubrovnik)
    
    # Flight connectivity constraints:
    for i in range(num_segments - 1):
        solver.add(allowed_flight(cities_vars[i], cities_vars[i+1]))
    
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        # Map each city to its fixed duration.
        fixed_durations = {
            "Mykonos": 4,
            "Krakow": 5,
            "Vilnius": 2,
            "Helsinki": 2,
            "Dubrovnik": 3,
            "Oslo": 2,
            "Madrid": 5,
            "Paris": 2
        }
        # Build the itinerary based on the solved segments.
        for i in range(num_segments):
            city_val = m.evaluate(cities_vars[i])
            start_day = m.evaluate(start_vars[i]).as_long()
            city_str = str(city_val)
            # Clean up the city name.
            for name in fixed_durations.keys():
                if name in city_str:
                    city_str = name
                    break
            dur = fixed_durations[city_str]
            end_day = start_day + dur - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_str})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()