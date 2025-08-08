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

# Try to avoid consecutive days in Split
s.push()
for i in range(1, 12):  # i from 1 to 11 (days 1 to 11 for the first day in the pair)
    split_day_i = Or(L[i-1] == Split, L[i] == Split)
    split_day_i1 = Or(L[i] == Split, L[i+1] == Split)
    s.add(Not(And(split_day_i, split_day_i1)))

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
    
    # Build itinerary
    itinerary = []
    for day in range(1, 13):
        city_prev = L_vals[day-1]
        city_curr = L_vals[day]
        if city_prev == city_curr:
            itinerary.append({"day": day, "place": city_prev})
        else:
            itinerary.append({"day": day, "place": city_prev})
            itinerary.append({"day": day, "place": city_curr})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    s.pop()
    if s.check() == sat:
        m = s.model()
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
        
        itinerary = []
        for day in range(1, 13):
            city_prev = L_vals[day-1]
            city_curr = L_vals[day]
            if city_prev == city_curr:
                itinerary.append({"day": day, "place": city_prev})
            else:
                itinerary.append({"day": day, "place": city_prev})
                itinerary.append({"day": day, "place": city_curr})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')