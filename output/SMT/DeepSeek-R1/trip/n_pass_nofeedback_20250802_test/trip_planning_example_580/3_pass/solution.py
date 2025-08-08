from z3 import *

# Define the duration variables for each city in the itinerary order
d0, d1, d2, d3, d4 = Ints('d0 d1 d2 d3 d4')
s = Solver()

# Each duration must be at least 3 days
s.add(d0 >= 3, d1 >= 3, d2 >= 3, d3 >= 3, d4 >= 3)

# The sum of all durations must be 23 days
s.add(d0 + d1 + d2 + d3 + d4 == 23)

# Avoid the solution where the first four cities each have exactly 3 days
s.add(Or(d0 > 3, d1 > 3, d2 > 3, d3 > 3))

if s.check() == sat:
    m = s.model()
    # Get the duration values
    durations = [
        m.eval(d0).as_long(),
        m.eval(d1).as_long(),
        m.eval(d2).as_long(),
        m.eval(d3).as_long(),
        m.eval(d4).as_long()
    ]
    # Calculate start and end days for each city
    starts = [1]
    ends = []
    for i in range(5):
        end = starts[i] + durations[i] - 1
        ends.append(end)
        if i < 4:
            starts.append(end + 1)
    # Verify the last day is 23
    if ends[-1] != 23:
        print("Error: The itinerary does not end on day 23.")
    else:
        # Define the cities in the itinerary order
        cities = ['Geneva', 'Paris', 'Porto', 'Reykjavik', 'Oslo']
        itinerary = []
        for i in range(5):
            day_range = f"Day {starts[i]}-{ends[i]}"
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        plan = {'itinerary': itinerary}
        print("Plan found:", plan)
else:
    print("No valid plan found.")