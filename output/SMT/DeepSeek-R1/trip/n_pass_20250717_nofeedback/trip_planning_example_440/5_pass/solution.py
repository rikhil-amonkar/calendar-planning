from z3 import *
import json

# Define the cities and their required days
cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
City, (Split, Helsinki, Reykjavik, Vilnius, Geneva) = EnumSort('City', cities)

# Flight connections (both directions)
flight_pairs = [
    (Split, Helsinki),
    (Geneva, Split),
    (Geneva, Helsinki),
    (Helsinki, Reykjavik),
    (Vilnius, Helsinki),
    (Split, Vilnius)
]
all_pairs = []
for (a, b) in flight_pairs:
    all_pairs.append((a, b))
    all_pairs.append((b, a))

# Required days for each city
req_days = {
    Split: 2,
    Helsinki: 2,
    Reykjavik: 3,
    Vilnius: 3,
    Geneva: 6
}

# Create solver and variables
s = Solver()
L = [Const(f'L_{i}', City) for i in range(13)]  # L[0] to L[12]

# Constraint: L[0] == L[1] (for day 1)
s.add(L[0] == L[1])

# Flight constraints for transitions
for i in range(1, 13):
    cond = Or([And(L[i-1] == a, L[i] == b) for (a, b) in all_pairs])
    s.add(If(L[i-1] != L[i], cond, True))

# Count constraints for each city
for city in [Split, Helsinki, Reykjavik, Vilnius, Geneva]:
    total = 0
    for i in range(1, 13):
        total += If(Or(L[i-1] == city, L[i] == city), 1, 0)
    s.add(total == req_days[city])

# Event constraints
# Reykjavik between day 10 and 12 (days 10,11,12 in itinerary)
s.add(Or(
    Or(L[9] == Reykjavik, L[10] == Reykjavik),  # day 10: L9 and L10
    Or(L[10] == Reykjavik, L[11] == Reykjavik),  # day 11: L10 and L11
    Or(L[11] == Reykjavik, L[12] == Reykjavik)  # day 12: L11 and L12
))

# Vilnius between day 7 and 9 (days 7,8,9 in itinerary)
s.add(Or(
    Or(L[6] == Vilnius, L[7] == Vilnius),  # day 7: L6 and L7
    Or(L[7] == Vilnius, L[8] == Vilnius),  # day 8: L7 and L8
    Or(L[8] == Vilnius, L[9] == Vilnius)   # day 9: L8 and L9
))

# Solve the problem
if s.check() == sat:
    m = s.model()
    # Map Z3 values to city names
    L_vals = []
    for i in range(13):
        val = m[L[i]]
        if val == Split:
            L_vals.append('Split')
        elif val == Helsinki:
            L_vals.append('Helsinki')
        elif val == Reykjavik:
            L_vals.append('Reykjavik')
        elif val == Vilnius:
            L_vals.append('Vilnius')
        elif val == Geneva:
            L_vals.append('Geneva')
        else:
            L_vals.append('Unknown')
    
    # Build city_days dictionary
    city_days = {
        'Split': set(),
        'Helsinki': set(),
        'Reykjavik': set(),
        'Vilnius': set(),
        'Geneva': set()
    }
    
    # For each day (1 to 12), add the day to both the start city and end city
    for day in range(1, 13):
        start_city = L_vals[day-1]
        end_city = L_vals[day]
        city_days[start_city].add(day)
        city_days[end_city].add(day)
    
    # Merge consecutive days for each city
    blocks = []
    for city in city_days:
        days = sorted(city_days[city])
        if not days:
            continue
        current_start = days[0]
        current_end = days[0]
        for i in range(1, len(days)):
            if days[i] == current_end + 1:
                current_end = days[i]
            else:
                if current_start == current_end:
                    blocks.append({'day_range': f'Day {current_start}', 'place': city})
                else:
                    blocks.append({'day_range': f'Day {current_start}-{current_end}', 'place': city})
                current_start = days[i]
                current_end = days[i]
        if current_start == current_end:
            blocks.append({'day_range': f'Day {current_start}', 'place': city})
        else:
            blocks.append({'day_range': f'Day {current_start}-{current_end}', 'place': city})
    
    # Sort blocks by the first day in the range
    def get_first_day(block):
        s = block['day_range'].split(' ')[1]
        if '-' in s:
            return int(s.split('-')[0])
        else:
            return int(s)
    
    blocks.sort(key=get_first_day)
    result = {"itinerary": blocks}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')