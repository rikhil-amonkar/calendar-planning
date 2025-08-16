from z3 import Solver, Int, If, And, Or, Distinct, sat
import json

# We “label” the cities with numbers:
# 0: Brussels
# 1: London
# 2: Venice
# 3: Lisbon
# 4: Reykjavik
# 5: Santorini
# 6: Madrid
city_names = {
    0: "Brussels",
    1: "London",
    2: "Venice",
    3: "Lisbon",
    4: "Reykjavik",
    5: "Santorini",
    6: "Madrid"
}
# The required number of days (including the flight overlap) in each city:
# (When you fly from one city to the next on the same day that day is counted in both segments.)
durations = {
    0: 2,  # Brussels – also covers the conference day1–2
    1: 3,  # London – 3 days
    2: 3,  # Venice – 3 days (and must include at least one day between day5 and day7)
    3: 4,  # Lisbon – 4 days
    4: 3,  # Reykjavik – 3 days
    5: 3,  # Santorini – 3 days
    6: 5   # Madrid – 5 days (wedding happens in Madrid between day 7 and day 11)
}

# Direct flight connections. Note that every bullet is “two‐way” except the one from Reykjavik to Madrid.
# We list each allowed ordered pair (a,b) that means a direct flight from city a to city b.
allowed_pairs = [
    # Venice <--> Madrid
    (2, 6), (6, 2),
    # Lisbon <--> Reykjavik
    (3, 4), (4, 3),
    # Brussels <--> Venice
    (0, 2), (2, 0),
    # Venice <--> Santorini
    (2, 5), (5, 2),
    # Lisbon <--> Venice
    (3, 2), (2, 3),
    # FROM Reykjavik TO Madrid (only one direction)
    (4, 6),
    # Brussels <--> London
    (0, 1), (1, 0),
    # Madrid <--> London
    (6, 1), (1, 6),
    # Santorini <--> London
    (5, 1), (1, 5),
    # London <--> Reykjavik
    (1, 4), (4, 1),
    # Brussels <--> Lisbon
    (0, 3), (3, 0),
    # Lisbon <--> London
    (3, 1), (1, 3),
    # Lisbon <--> Madrid
    (3, 6), (6, 3),
    # Madrid <--> Santorini
    (6, 5), (5, 6),
    # Brussels <--> Reykjavik
    (0, 4), (4, 0),
    # Brussels <--> Madrid
    (0, 6), (6, 0),
    # Venice <--> London
    (2, 1), (1, 2)
]

# A helper function that returns the required duration given a city (represented by an Int).
def duration(city):
    # City is an integer. We use nested If’s to return the proper duration.
    return If(city == 0, 2,
           If(city == 1, 3,
           If(city == 2, 3,
           If(city == 3, 4,
           If(city == 4, 3,
           If(city == 5, 3, 5))))))

# The itinerary is made of 7 segments – one per city.
num_segments = 7

# Decision variables:
# order[i] is the city visited as the i-th segment.
order = [Int(f"order_{i}") for i in range(num_segments)]
# The starting day s[i] for segment i.
s = [Int(f"s_{i}") for i in range(num_segments)]

solver = Solver()

# 1. The permutation: each city must appear once and Brussels (0) is fixed as first.
solver.add(order[0] == 0)
for i in range(num_segments):
    solver.add(order[i] >= 0, order[i] <= 6)
solver.add(Distinct(order))

# 2. Define the starting days.
# The first segment starts on day 1.
solver.add(s[0] == 1)
# For segments i>=1, the start day is the last day of the previous segment,
# because when you fly on that matching day it is counted for both cities.
for i in range(1, num_segments):
    solver.add(s[i] == s[i-1] + duration(order[i-1]) - 1)

# 3. The last segment must “finish” on day 17.
# That is: s[last] + duration(last) - 1 == 17.
solver.add(s[num_segments-1] + duration(order[num_segments-1]) - 1 == 17)

# 4. Flight connectivity constraint.
# For every consecutive pair, the flight taken must be a direct flight.
for i in range(num_segments - 1):
    # Build an Or-condition stating that the pair (order[i], order[i+1])
    # equals one of the allowed pairs.
    possible = []
    for (a, b) in allowed_pairs:
        possible.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(possible))

# 5. Extra time–window constraints:
# (a) You want to spend 3 days in Venice.
#     You plan to visit relatives in Venice sometime between day 5 and day 7.
# That means that if the city in any segment is Venice (2),
# then its segment [s, s+duration-1] must intersect [5,7].
for i in range(num_segments):
    # For Venice: [s, s+2] (since duration=3) must have a common day with [5,7].
    # A sufficient constraint is to require s[i] <= 7 and s[i] + 3 - 1 >= 5.
    solver.add(If(order[i] == 2, And(s[i] <= 7, s[i] + 2 >= 5), True))
    
# (b) You want to spend 5 days in Madrid and attend a wedding there between day 7 and day 11.
# For Madrid (6) the segment [s, s+4] must intersect [7,11].
for i in range(num_segments):
    solver.add(If(order[i] == 6, And(s[i] <= 11, s[i] + 4 >= 7), True))

# Solve the model.
if solver.check() == sat:
    m = solver.model()
    
    # Retrieve the chosen order and segment starting days.
    chosen_order = [m.evaluate(order[i]).as_long() for i in range(num_segments)]
    chosen_s = [m.evaluate(s[i]).as_long() for i in range(num_segments)]
    
    # For convenience, compute the (start, end) days for each segment.
    segments = []
    for i in range(num_segments):
        city = chosen_order[i]
        seg_start = chosen_s[i]
        seg_duration = durations[city]  # durations from our dictionary are fixed
        seg_end = seg_start + seg_duration - 1
        segments.append((city, seg_start, seg_end))
    
    # Build a day-by-day itinerary.
    # Note: on a flight day the day belongs to two segments (the end of one and the beginning of the next).
    day_itinerary = {}
    for day in range(1, 18):  # days 1 to 17
        places_today = []
        for seg_index, (city, seg_start, seg_end) in enumerate(segments):
            if seg_start <= day <= seg_end:
                places_today.append((seg_index, city_names[city]))
        # Order the places by the segment order (so that on shared days the earlier segment shows up first).
        places_today.sort(key=lambda x: x[0])
        # Join the names (if more than one, separate by a comma)
        day_description = ", ".join([place for idx, place in places_today])
        day_itinerary[day] = day_description

    # Build the final JSON output: a list of day mappings.
    itinerary_list = []
    for day in range(1, 18):
        itinerary_list.append({"day": day, "place": day_itinerary[day]})
    
    output = {"itinerary": itinerary_list}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")