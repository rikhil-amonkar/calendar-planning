from z3 import *
import json

def main():
    s = Solver()
    num_days = 9
    # We have four cities. We use integers to represent them:
    # 0: Vienna, 1: Stockholm, 2: Nice, 3: Split
    cities = ["Vienna", "Stockholm", "Nice", "Split"]
    num_cities = len(cities)

    # Create variables for each day.
    # x[i] : the base city (“stay”) on day i (0-indexed => day i+1)
    # f[i] : a Boolean that indicates whether you take a flight on day i.
    # y[i] : if f[i] is true then the flight destination on day i.
    x = [Int(f"x_{i}") for i in range(num_days)]
    f_vars = [Bool(f"f_{i}") for i in range(num_days)]
    y = [Int(f"y_{i}") for i in range(num_days)]
    
    # Domain constraints: every x[i] and y[i] must be a city index [0,3].
    for i in range(num_days):
        s.add(And(x[i] >= 0, x[i] < num_cities))
        s.add(And(y[i] >= 0, y[i] < num_cities))
    
    # Exactly three days are flight days. (Remember: when you fly the day counts twice.)
    s.add(Sum([If(f_vars[i], 1, 0) for i in range(num_days)]) == 3)
    
    # Transition constraints:
    # For i = 0,..,7, if you fly on day i then you arrive at y[i] and so x[i+1] = y[i];
    # otherwise you remain in the same city (x[i+1] = x[i]).
    for i in range(num_days - 1):
        s.add(If(f_vars[i], x[i+1] == y[i], x[i+1] == x[i]))
    
    # Allowed direct–flight pairs.
    # Only the following pairs (in either direction) are allowed:
    # Vienna–Stockholm, Vienna–Nice, Vienna–Split, Stockholm–Split, and Nice–Stockholm.
    allowed_flights = [(0, 1), (1, 0),
                         (0, 2), (2, 0),
                         (0, 3), (3, 0),
                         (1, 3), (3, 1),
                         (1, 2), (2, 1)]
    for i in range(num_days):
        # If you fly on day i, then you must change cities and the pair must be allowed.
        s.add(Implies(f_vars[i], x[i] != y[i]))
        allowed_expr = []
        for (a, b) in allowed_flights:
            allowed_expr.append(And(x[i] == a, y[i] == b))
        s.add(Implies(f_vars[i], Or(*allowed_expr)))
    
    # Now add the “stay–days” count constraints.
    # If you do not fly on day i, then you count 1 day in city x[i];
    # if you fly, then that day counts for both x[i] and y[i].
    required_counts = {0: 2, 1: 5, 2: 2, 3: 3}  # Vienna:2, Stockholm:5, Nice:2, Split:3
    for city in range(num_cities):
        count_expr = Sum([If(f_vars[i],
                             If(x[i] == city, 1, 0) + If(y[i] == city, 1, 0),
                             If(x[i] == city, 1, 0)
                             ) for i in range(num_days)])
        s.add(count_expr == required_counts[city])
    
    # Workshop in Vienna must be attended on either day 1 or day 2.
    # (That is, at least one of these days the traveler must be in Vienna.)
    workshop_day0 = Or(x[0] == 0, And(f_vars[0], y[0] == 0))
    workshop_day1 = Or(x[1] == 0, And(f_vars[1], y[1] == 0))
    s.add(Or(workshop_day0, workshop_day1))
    
    # Conference in Split must be attended on day 7 and day 9.
    # (Remember: days are 0-indexed so day 7 is index 6 and day 9 is index 8.)
    s.add(Or(x[6] == 3, And(f_vars[6], y[6] == 3)))  # day 7
    s.add(Or(x[8] == 3, And(f_vars[8], y[8] == 3)))  # day 9

    # Check for a solution ...
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_days):
            day_entry = {"day": i+1, "places": []}
            # add the “base” city in x[i]
            base_city = m[x[i]].as_long() if m[x[i]] is not None else None
            if base_city is not None:
                day_entry["places"].append(cities[base_city])
            # if a flight is taken on that day then also record the arrival city y[i]
            if is_true(m.evaluate(f_vars[i])):
                arrival_city = m[y[i]].as_long()
                day_entry["places"].append(cities[arrival_city])
            itinerary.append(day_entry)
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()