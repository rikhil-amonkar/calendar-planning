from z3 import *

# Create the solver
s = Solver()

# We have 14 days
n_days = 14

# Create an array of integer variables for the 14 days: c[0] is day1, c[1] is day2, ... c[13] is day14
c = [Int(f"c_{i}") for i in range(n_days)]

# Each day must be an integer between 0 and 5 (inclusive)
for i in range(n_days):
    s.add(c[i] >= 0)
    s.add(c[i] <= 5)

# Constraints for the sequence:
# 1. Start at Helsinki (0) on day1
s.add(c[0] == 0)

# 2. The sequence must be non-decreasing by at most 1 at each step: either stay in the same city or move to the next city
for i in range(n_days - 1):
    s.add(Or(c[i+1] == c[i], c[i+1] == c[i] + 1))

# 3. We must end at Split (5) on the last day
s.add(c[13] == 5)

# 4. At least 3 days in Madrid (1), Budapest (2), Reykjavik (3), Warsaw (4)
for city_index in [1, 2, 3, 4]:
    s.add(Sum([If(c[i] == city_index, 1, 0) for i in range(n_days)]) >= 3)

# 5. At least 1 day in Split (5) - already ensured by ending at Split? But we might have more than one day? 
# But we require at least one day and we have the last day, so it's at least one. So we don't need an extra constraint? 
# However, we might have more than one day? But the constraint above (ending at Split) does not ensure at least one day? 
# Actually, because we are at Split on the last day, we have at least one day? But what if we are in Split only on the last day? Then it's one day. 
# So we are safe.

# List of city names
city_names = ['Helsinki', 'Madrid', 'Budapest', 'Reykjavik', 'Warsaw', 'Split']

# Check if the solver can find a solution
if s.check() == sat:
    m = s.model()
    # Get the value for each day
    itinerary_indices = [m.evaluate(c[i]).as_long() for i in range(n_days)]
    # Map indices to city names and create the itinerary as a list of lists
    itinerary = [[city_names[idx]] for idx in itinerary_indices]
    print(itinerary)
else:
    print("No solution found")