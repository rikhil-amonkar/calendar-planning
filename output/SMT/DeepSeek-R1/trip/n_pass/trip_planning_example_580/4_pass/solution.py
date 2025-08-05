from z3 import *

# Define duration variables for each city in itinerary order
d0, d1, d2, d3, d4 = Ints('d0 d1 d2 d3 d4')
s = Solver()

# Minimum stays (Oslo must be at least 4 days)
s.add(d0 >= 3, d1 >= 3, d2 >= 3, d3 >= 3, d4 >= 4)

# Maximum stay limit (prevent overly long stays)
s.add(d0 <= 7, d1 <= 7, d2 <= 7, d3 <= 7, d4 <= 7)

# Total trip days
s.add(d0 + d1 + d2 + d3 + d4 == 23)

# At least one non-Oslo city has >3 days
s.add(Or(d0 > 3, d1 > 3, d2 > 3, d3 > 3))

if s.check() == sat:
    m = s.model()
    durations = [
        m.eval(d0).as_long(),
        m.eval(d1).as_long(),
        m.eval(d2).as_long(),
        m.eval(d3).as_long(),
        m.eval(d4).as_long()
    ]
    # Calculate day ranges
    starts = [1]
    ends = []
    for i in range(5):
        end = starts[i] + durations[i] - 1
        ends.append(end)
        if i < 4:
            starts.append(end + 1)
    # Verify solution
    if ends[-1] != 23:
        print("Invalid plan: Doesn't end on day 23")
    else:
        cities = ['Geneva', 'Paris', 'Porto', 'Reykjavik', 'Oslo']
        itinerary = []
        for i in range(5):
            day_range = f"Day {starts[i]}-{ends[i]}"
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        plan = {'itinerary': itinerary}
        print("Plan found:", plan)
else:
    print("No valid plan found")