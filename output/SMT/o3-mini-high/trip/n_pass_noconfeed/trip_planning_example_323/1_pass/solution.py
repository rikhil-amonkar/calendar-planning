import json
from z3 import *

def main():
    solver = Solver()
    
    # Define the 4 segments. Each segment will have a city value and a start day.
    # Cities are encoded as: 0: London, 1: Oslo, 2: Split, 3: Porto.
    cities = [Int(f"city_{i}") for i in range(4)]
    starts = [Int(f"start_{i}") for i in range(4)]
    
    # Domain constraints for cities: each city must be one of 0,1,2,3.
    for c in cities:
        solver.add(Or(c == 0, c == 1, c == 2, c == 3))
    
    # All cities must be visited exactly once.
    solver.add(Distinct(cities))
    
    # Define the duration for each city visit.
    # London:7, Oslo:2, Split:5, Porto:5.
    def duration(city):
        return If(city == 0, 7, If(city == 1, 2, If(city == 2, 5, 5)))
    
    # Trip starts on day 1.
    solver.add(starts[0] == 1)
    
    # If you fly from city A to city B on day X, you're in both cities on day X.
    # Thus, if segment i (in city A) lasts d days, then segment i+1 starts on the same day
    # as the last day of segment i.
    for i in range(3):
        solver.add(starts[i+1] == starts[i] + duration(cities[i]) - 1)
    
    # Total trip days is 16:
    solver.add(starts[3] + duration(cities[3]) - 1 == 16)
    
    # Direct flight constraints.
    # Allowed direct flights (bidirectional) are:
    # London <-> Oslo, Split <-> Oslo, Oslo <-> Porto, London <-> Split.
    for i in range(3):
        a = cities[i]
        b = cities[i+1]
        allowed_flight = Or(
            And(a == 0, b == 1),
            And(a == 1, b == 0),
            And(a == 2, b == 1),
            And(a == 1, b == 2),
            And(a == 1, b == 3),
            And(a == 3, b == 1),
            And(a == 0, b == 2),
            And(a == 2, b == 0)
        )
        solver.add(allowed_flight)
    
    # Constraint: The annual show in Split is from day 7 to day 11.
    # To cover 5 days (the planned stay in Split) and include days 7 to 11,
    # the Split segment must start exactly on day 7.
    for i in range(4):
        solver.add(Implies(cities[i] == 2, starts[i] == 7))
    
    # Constraint: Visit relatives in London between day 1 and day 7.
    # Thus, if a segment is in London, then its start day must be on or before day 7.
    for i in range(4):
        solver.add(Implies(cities[i] == 0, starts[i] <= 7))
    
    # Solve for a valid itinerary based on the constraints.
    if solver.check() == sat:
        model = solver.model()
        # Map the integer codes to city names.
        city_names = {0: "London", 1: "Oslo", 2: "Split", 3: "Porto"}
        itinerary = []
        for i in range(4):
            start_day = model.evaluate(starts[i]).as_long()
            dur = model.evaluate(duration(cities[i])).as_long()
            end_day = start_day + dur - 1
            city_val = model.evaluate(cities[i]).as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_val]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no valid itinerary is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()