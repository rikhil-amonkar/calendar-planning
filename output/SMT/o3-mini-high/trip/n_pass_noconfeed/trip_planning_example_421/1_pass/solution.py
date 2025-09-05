from z3 import *
import json

def main():
    # Number of segments (cities) in the itinerary
    n = 5

    # Create Z3 integer variables for the city at each segment (0: Nice, 1: Krakow, 2: Dublin, 3: Lyon, 4: Frankfurt)
    itinerary = [Int(f"city_{i}") for i in range(n)]
    # Create Z3 integer variables for the start day of each segment
    s = [Int(f"s_{i}") for i in range(n)]
    
    # A helper function that returns the fixed duration for a given city (using an If chain)
    def city_duration(city):
        return If(city == 0, 5,   # Nice: 5 days
               If(city == 1, 6,   # Krakow: 6 days
               If(city == 2, 7,   # Dublin: 7 days
               If(city == 3, 4,   # Lyon: 4 days
               If(city == 4, 2, 0)))))

    # Mapping of city indices to names
    city_names = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    
    solver = Solver()

    # Domain constraints: each itinerary city variable must be between 0 and 4.
    for i in range(n):
        solver.add(itinerary[i] >= 0, itinerary[i] <= 4)
    # The itinerary must visit all five cities exactly once.
    solver.add(Distinct(itinerary))
    
    # The trip starts on day 1.
    solver.add(s[0] == 1)
    for i in range(n):
        solver.add(s[i] > 0)
    
    # Flight transitions:
    # If you fly from city A -> city B on day X then you are in A and in B on day X.
    # This is modeled by letting the next segment start on the same day as the previous segment's last day.
    # So for each segment (except the last), we have:
    #   s[i+1] == s[i] + duration(city[i]) - 1
    for i in range(n - 1):
        solver.add(s[i+1] == s[i] + city_duration(itinerary[i]) - 1)
    
    # The entire trip must span 20 days:
    # Last segment finishes on day: s[n-1] + duration(city[n-1]) - 1 == 20.
    solver.add(s[n-1] + city_duration(itinerary[n-1]) - 1 == 20)
    
    # Special constraints:
    # 1. In Nice (city 0) you visit relatives between day 1 and day 5.
    #    This is enforced by requiring the start day for Nice to be no later than day 5.
    for i in range(n):
        solver.add(Implies(itinerary[i] == 0, s[i] <= 5))
    
    # 2. In Frankfurt (city 4) you meet friends between day 19 and day 20.
    #    Since Frankfurt lasts 2 days, its interval [s, s+1] must include at least one day in [19,20].
    #    That is, we require: s[i] + 2 - 1 >= 19  ->  s[i] + 1 >= 19.
    for i in range(n):
        solver.add(Implies(itinerary[i] == 4, s[i] + 1 >= 19))
    
    # Allowed direct flight connections (bidirectional) are:
    # Nice <-> Dublin, Dublin <-> Frankfurt, Dublin <-> Krakow,
    # Krakow <-> Frankfurt, Lyon <-> Frankfurt, Nice <-> Frankfurt,
    # Lyon <-> Dublin, Nice <-> Lyon.
    allowed_pairs = [
        (0, 2), (2, 0),   # Nice and Dublin
        (2, 4), (4, 2),   # Dublin and Frankfurt
        (2, 1), (1, 2),   # Dublin and Krakow
        (1, 4), (4, 1),   # Krakow and Frankfurt
        (3, 4), (4, 3),   # Lyon and Frankfurt
        (0, 4), (4, 0),   # Nice and Frankfurt
        (3, 2), (2, 3),   # Lyon and Dublin
        (0, 3), (3, 0)    # Nice and Lyon
    ]
    # For each flight (transition between segments), assert that the consecutive cities have a direct flight.
    for i in range(n - 1):
        conditions = []
        for (a, b) in allowed_pairs:
            conditions.append(And(itinerary[i] == a, itinerary[i+1] == b))
        solver.add(Or(conditions))
    
    # Solve the SMT constraints.
    if solver.check() == sat:
        model = solver.model()
        result = {"itinerary": []}
        for i in range(n):
            city_val = model.evaluate(itinerary[i]).as_long()
            start_day = model.evaluate(s[i]).as_long()
            # Use the fixed durations defined for each city.
            if city_val == 0:
                dur = 5
            elif city_val == 1:
                dur = 6
            elif city_val == 2:
                dur = 7
            elif city_val == 3:
                dur = 4
            elif city_val == 4:
                dur = 2
            finish_day = start_day + dur - 1
            result["itinerary"].append({
                "day_range": f"Day {start_day}-{finish_day}",
                "place": city_names[city_val]
            })
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()