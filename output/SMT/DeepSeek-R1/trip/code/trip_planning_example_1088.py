from z3 import *

# Cities encoding
Reykjavik, Oslo, Stuttgart, Split, Geneva, Porto, Tallinn, Stockholm = 0, 1, 2, 3, 4, 5, 6, 7
city_names = {
    0: 'Reykjavik',
    1: 'Oslo',
    2: 'Stuttgart',
    3: 'Split',
    4: 'Geneva',
    5: 'Porto',
    6: 'Tallinn',
    7: 'Stockholm'
}

# Required days per city
required_days = {
    Reykjavik: 2,
    Oslo: 5,
    Stuttgart: 5,
    Split: 3,
    Geneva: 2,
    Porto: 3,
    Tallinn: 5,
    Stockholm: 3
}

# Direct flights (each pair is bidirectional)
direct_flights = [
    (Reykjavik, Stuttgart), (Stuttgart, Reykjavik),
    (Reykjavik, Stockholm), (Stockholm, Reykjavik),
    (Reykjavik, Tallinn), (Tallinn, Reykjavik),
    (Stockholm, Oslo), (Oslo, Stockholm),
    (Stuttgart, Porto), (Porto, Stuttgart),
    (Oslo, Split), (Split, Oslo),
    (Stockholm, Stuttgart), (Stuttgart, Stockholm),
    (Reykjavik, Oslo), (Oslo, Reykjavik),
    (Oslo, Geneva), (Geneva, Oslo),
    (Stockholm, Split), (Split, Stockholm),
    (Split, Stuttgart), (Stuttgart, Split),
    (Tallinn, Oslo), (Oslo, Tallinn),
    (Stockholm, Geneva), (Geneva, Stockholm),
    (Oslo, Porto), (Porto, Oslo),
    (Geneva, Porto), (Porto, Geneva),
    (Geneva, Split), (Split, Geneva)
]

# Create Z3 variables for each day (0-based, days 0-20 correspond to days 1-21)
days = [Int(f'day_{i}') for i in range(21)]

s = Solver()

# Constraint: Days 0 and 1 (days 1 and 2) must be Reykjavik
s.add(days[0] == Reykjavik)
s.add(days[1] == Reykjavik)

# Constraint: Days 18, 19, 20 (days 19-21) must be Porto
s.add(days[18] == Porto)
s.add(days[19] == Porto)
s.add(days[20] == Porto)

# Friend meeting in Stockholm between day 2 and 4 (indices 1-3)
# At least one of days 2 or 3 (days 3 or 4) must be Stockholm
s.add(Or(days[2] == Stockholm, days[3] == Stockholm))

# Constraints for consecutive days
for i in range(20):
    current = days[i]
    next_day = days[i+1]
    # Either stay in the same city or fly directly
    s.add(Or(
        current == next_day,
        Or([And(current == a, next_day == b) for (a, b) in direct_flights])
    ))

# Compute total days for each city
for city in range(8):
    count_list = Sum([If(days[i] == city, 1, 0) for i in range(21)])
    count_flights = Sum([If(And(days[i] != days[i+1], Or(days[i] == city, days[i+1] == city)), 1, 0) for i in range(20)])
    total = count_list + count_flights
    s.add(total == required_days[city])

# Solve the model
if s.check() == sat:
    model = s.model()
    schedule = [model.evaluate(days[i]).as_long() for i in range(21)]
    # Print the schedule
    for idx, city_num in enumerate(schedule, 1):
        print(f'Day {idx}: {city_names[city_num]}')
else:
    print("No valid schedule found.")