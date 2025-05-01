from z3 import *

# Create solver
s = Solver()

# Days are 1-14, represented as integers 1-3 for cities
days = 14
city = [Int(f'city_{i}') for i in range(1, days+1)]

# Each day must be Barcelona (1), Florence (2), or Helsinki (3)
for d in city:
    s.add(Or(d == 1, d == 2, d == 3))

# Total days constraints
s.add(Sum([If(c == 1, 1, 0) for c in city]) == 5)  # Barcelona: 5 days
s.add(Sum([If(c == 2, 1, 0) for c in city]) == 6)  # Florence: 6 days
s.add(Sum([If(c == 3, 1, 0) for c in city]) == 5)  # Helsinki: 5 days

# Direct flight transitions (Barcelona <-> Florence, Barcelona <-> Helsinki)
for i in range(days-1):
    current = city[i]
    next_city = city[i+1]
    s.add(Implies(current != next_city, 
                 Or(And(current == 1, next_city == 2),
                    And(current == 2, next_city == 1),
                    And(current == 1, next_city == 3),
                    And(current == 3, next_city == 1))))

# At least one day in Florence between day 9-14 (indices 8-13)
s.add(Or([city[i] == 2 for i in range(8, 14)]))

# Check and output
if s.check() == sat:
    m = s.model()
    schedule = []
    for d in city:
        schedule.append(m[d].as_long())
    # Convert to city names
    city_names = {1: 'Barcelona', 2: 'Florence', 3: 'Helsinki'}
    day_plan = []
    current_city = schedule[0]
    start_day = 1
    for i in range(1, days):
        if schedule[i] != current_city:
            day_plan.append(f"{city_names[current_city]} days {start_day}-{i}")
            current_city = schedule[i]
            start_day = i+1
    day_plan.append(f"{city_names[current_city]} days {start_day}-{days}")
    print("Valid itinerary:")
    print("\n".join(day_plan))
else:
    print("No solution found")