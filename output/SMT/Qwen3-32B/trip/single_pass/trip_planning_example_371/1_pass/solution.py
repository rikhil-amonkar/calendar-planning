import json
from z3 import *

# Define cities as integers
NICE = 0
STOCKHOLM = 1
SPLIT = 2
VIENNA = 3

days = 9
day_vars = [Int(f'day_{i+1}') for i in range(days)]

solver = Solver()

# Constraints for consecutive days
for d in range(1, days):  # d is from 1 to 8 (0-based in day_vars)
    prev_day = day_vars[d-1]
    curr_day = day_vars[d]
    # If previous and current are different, then the transition is allowed
    cond = Or(prev_day == curr_day,
              And(prev_day == VIENNA, curr_day == STOCKHOLM),
              And(prev_day == STOCKHOLM, curr_day == VIENNA),
              And(prev_day == VIENNA, curr_day == NICE),
              And(prev_day == NICE, curr_day == VIENNA),
              And(prev_day == VIENNA, curr_day == SPLIT),
              And(prev_day == SPLIT, curr_day == VIENNA),
              And(prev_day == STOCKHOLM, curr_day == SPLIT),
              And(prev_day == SPLIT, curr_day == STOCKHOLM),
              And(prev_day == NICE, curr_day == STOCKHOLM),
              And(prev_day == STOCKHOLM, curr_day == NICE))
    solver.add(cond)

# Constraints for day 1, 7, 9
solver.add(day_vars[0] == VIENNA)
solver.add(day_vars[6] == SPLIT)
solver.add(day_vars[8] == SPLIT)

# Required total days
required_days = {
    NICE: 2,
    STOCKHOLM: 5,
    SPLIT: 3,
    VIENNA: 2
}

for city in [NICE, STOCKHOLM, SPLIT, VIENNA]:
    total_days = 0
    # Day 1
    total_days += If(day_vars[0] == city, 1, 0)
    # Days 2 to 9
    for d in range(1, days):
        prev_day = day_vars[d-1]
        curr_day = day_vars[d]
        contribution = If(prev_day == curr_day,
                          If(curr_day == city, 1, 0),
                          If(curr_day == city, 1, 0) + If(prev_day == city, 1, 0))
        total_days += contribution
    solver.add(total_days == required_days[city])

if solver.check() == sat:
    model = solver.model()
    itinerary = []
    city_names = {NICE: "Nice", STOCKHOLM: "Stockholm", SPLIT: "Split", VIENNA: "Vienna"}
    for i in range(days):
        day_num = i + 1
        city_id = model[day_vars[i]].as_long()
        city_name = city_names[city_id]
        itinerary.append({"day": day_num, "city": city_name})
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")