from z3 import *

d0, d1, d2, d3, d4 = Ints('d0 d1 d2 d3 d4')  # Durations for each city
s = Solver()

# Minimum stays (Oslo must be at least 4 days)
s.add(d0 >= 3, d1 >= 3, d2 >= 3, d3 >= 3, d4 >= 4)

# Maximum stay limit (prevent overly long stays)
s.add(d0 <= 6, d1 <= 6, d2 <= 6, d3 <= 6, d4 <= 6)

# Total trip must be exactly 23 days
s.add(d0 + d1 + d2 + d3 + d4 == 23)

# At least one non-Oslo city must have >3 days
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
    for i, days in enumerate(durations):
        end = starts[i] + days - 1
        ends.append(end)
        if i < 4:  # Not last city
            starts.append(end + 1)  # Next city starts the following day
            
    cities = ['Geneva', 'Paris', 'Porto', 'Reykjavik', 'Oslo']
    itinerary = []
    for i in range(5):
        day_range = f"Day {starts[i]}-{ends[i]}"
        itinerary.append({'day_range': day_range, 'place': cities[i]})
    
    plan = {'itinerary': itinerary}
    print("Plan found:", plan)
else:
    print("No valid plan found")