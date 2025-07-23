from z3 import *

# Create solver
s = Solver()

# Create 13 variables: c0 to c12
c = [Int('c%d' % i) for i in range(0, 13)]

# Each variable must be 0, 1, or 2 (Milan, Seville, Naples)
for i in range(0, 13):
    s.add(Or(c[i] == 0, c[i] == 1, c[i] == 2))

# Start in Naples (city 2)
s.add(c[0] == 2)

# Direct flight constraints for i from 0 to 11: if c[i] != c[i+1], then the pair must be (0,1), (1,0), (0,2), (2,0)
for i in range(0, 12):
    s.add(If(
        c[i] != c[i+1],
        Or(
            And(c[i] == 0, c[i+1] == 1),
            And(c[i] == 1, c[i+1] == 0),
            And(c[i] == 0, c[i+1] == 2),
            And(c[i] == 2, c[i+1] == 0)
        ),
        True
    ))

# Constraints for Seville from day9 to day12: c9, c10, c11, c12 must be 1 (Seville)
s.add(c[9] == 1)
s.add(c[10] == 1)
s.add(c[11] == 1)
s.add(c[12] == 1)

# Define counts for each city
# For Milan (0)
count0_milan = Sum([If(c[i] == 0, 1, 0) for i in range(0, 12)])  # start cities: c0 to c11
count1_milan = Sum([If(And(c[i] == 0, c[i-1] != 0), 1, 0) for i in range(1, 13)])  # end cities: c1 to c12, with condition
total_milan = count0_milan + count1_milan
s.add(total_milan == 7)

# For Seville (1)
count0_seville = Sum([If(c[i] == 1, 1, 0) for i in range(0, 12)])
count1_seville = Sum([If(And(c[i] == 1, c[i-1] != 1), 1, 0) for i in range(1, 13)])
total_seville = count0_seville + count1_seville
s.add(total_seville == 4)

# For Naples (2)
count0_naples = Sum([If(c[i] == 2, 1, 0) for i in range(0, 12)])
count1_naples = Sum([If(And(c[i] == 2, c[i-1] != 2), 1, 0) for i in range(1, 13)])
total_naples = count0_naples + count1_naples
s.add(total_naples == 3)

# Check and get the model
if s.check() == sat:
    model = s.model()
    c_values = [model.evaluate(c[i]) for i in range(0, 13)]
    # Group consecutive days with the same end city (c1 to c12) into segments
    segments = []
    start_day = 1
    current_city = c_values[1]  # c1 is end of day1
    for day in range(1, 13):
        if day == 12:  # Last day
            segments.append((start_day, 12, current_city))
            break
        if c_values[day] != c_values[day+1]:
            end_day = day
            segments.append((start_day, end_day, current_city))
            start_day = day + 1
            current_city = c_values[day+1]
    # Format the segments
    city_names = {0: "Milan", 1: "Seville", 2: "Naples"}
    itinerary = []
    for seg in segments:
        start, end, city = seg
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({'day_range': day_range, 'place': city_names[city.as_long()]})
    result = {'itinerary': itinerary}
    print(result)
else:
    print("No solution found")