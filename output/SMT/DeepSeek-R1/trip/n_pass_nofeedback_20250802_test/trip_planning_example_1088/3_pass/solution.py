import z3
import json

# Define the City enum type
City, (Reykjavik, Stockholm, Oslo, Tallinn, Stuttgart, Split, Geneva, Porto) = \
    z3.EnumSort('City', ['Reykjavik', 'Stockholm', 'Oslo', 'Tallinn', 'Stuttgart', 'Split', 'Geneva', 'Porto'])

# Define the allowed direct flights (both directions)
allowed_flights = [
    (Reykjavik, Stuttgart),
    (Reykjavik, Stockholm),
    (Reykjavik, Tallinn),
    (Stockholm, Oslo),
    (Stuttgart, Porto),
    (Oslo, Split),
    (Stockholm, Stuttgart),
    (Reykjavik, Oslo),
    (Oslo, Geneva),
    (Stockholm, Split),
    (Split, Stuttgart),
    (Tallinn, Oslo),
    (Stockholm, Geneva),
    (Oslo, Porto),
    (Geneva, Porto),
    (Geneva, Split)
]

allowed_pairs = set()
for a, b in allowed_flights:
    allowed_pairs.add((a, b))
    allowed_pairs.add((b, a))

# Create variables for the end city of each day (21 days)
c = [z3.Const(f'c_{i}', City) for i in range(21)]

solver = z3.Solver()

# Fixed constraints
solver.add(c[0] == Reykjavik)  # Day 1 must end in Reykjavik
solver.add(c[18] == Porto)      # Day 19 must end in Porto
solver.add(c[19] == Porto)      # Day 20 must end in Porto
solver.add(c[20] == Porto)      # Day 21 must end in Porto

# Meeting in Stockholm between day 2 and day 4: must be present on at least one of these days
# Presence on day i is defined as: either the start of the day (end of previous day) or the end of the day is Stockholm.
# Day2: start = c[0] (end of day1), end = c[1]
# Day3: start = c[1], end = c[2]
# Day4: start = c[2], end = c[3]
presence_day2 = z3.Or(c[0] == Stockholm, c[1] == Stockholm)
presence_day3 = z3.Or(c[1] == Stockholm, c[2] == Stockholm)
presence_day4 = z3.Or(c[2] == Stockholm, c[3] == Stockholm)
solver.add(z3.Or(presence_day2, presence_day3, presence_day4))

# Flight constraints: consecutive days must be either the same city or connected by a direct flight
for i in range(20):
    solver.add(z3.Or(
        c[i] == c[i+1],
        z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_pairs])
    ))

# Total days per city: count a day for a city if the city is the start or end of the day.
def total_days(city):
    total = 0
    # Day1: start is Reykjavik (fixed), end is c[0]
    total += z3.If(z3.Or(Reykjavik == city, c[0] == city), 1, 0)
    # Days 2 to 21: for day i (1-indexed), start = c[i-2] for i>=2, but we index by the segment between days
    # For segment i (0-indexed segment index, which is between day i and day i+1): 
    #   For day i+1, the start is c[i] and the end is c[i+1]
    for i in range(0, 20):   # i from 0 to 19: representing segments between day1-day2 up to day20-day21
        # This segment corresponds to day (i+2) if we think about the day that ends at c[i+1]? 
        # Actually, the segment from day (i) to day (i+1) (0-indexed) is for the presence on day (i+1) in terms of start and end?
        # But note: the presence on day (i+1) is determined by the start (c[i]) and end (c[i+1]).
        total += z3.If(z3.Or(c[i] == city, c[i+1] == city), 1, 0)
    return total

solver.add(total_days(Reykjavik) == 2)
solver.add(total_days(Oslo) == 5)
solver.add(total_days(Stuttgart) == 5)
solver.add(total_days(Split) == 3)
solver.add(total_days(Geneva) == 2)
solver.add(total_days(Porto) == 3)
solver.add(total_days(Tallinn) == 5)
solver.add(total_days(Stockholm) == 3)

# Solve the problem
if solver.check() == z3.sat:
    model = solver.model()
    c_vals = [model.eval(c_i) for c_i in c]
    
    itinerary = []
    # Day 1: start in Reykjavik, end in c[0]
    start1 = Reykjavik
    end1 = c_vals[0]
    if start1.eq(end1):
        cities_list = [str(start1)]
    else:
        cities_list = sorted([str(start1), str(end1)])
    itinerary.append({"day": 1, "city": cities_list})
    
    # Days 2 to 21: for day i (1-indexed i>=2), start = c[i-2], end = c[i-1]
    for i in range(1, 21):
        start_city = c_vals[i-1]
        end_city = c_vals[i]
        if start_city.eq(end_city):
            cities_list = [str(start_city)]
        else:
            cities_list = sorted([str(start_city), str(end_city)])
        itinerary.append({"day": i+1, "city": cities_list})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No solution found"}))