import z3
import json

# Define cities as integers: 0 - Vilnius, 1 - Munich, 2 - Mykonos
first = z3.Int('first')
second = z3.Int('second')
third = z3.Int('third')

s = z3.Solver()

# All cities must be distinct
s.add(z3.Distinct(first, second, third))

# Allowed transitions: (Vilnius, Munich), (Munich, Vilnius), (Munich, Mykonos), (Mykonos, Munich)
allowed_transitions = [(0, 1), (1, 0), (1, 2), (2, 1)]

# Transition between first and second city
trans1 = z3.Or([z3.And(first == a, second == b) for a, b in allowed_transitions])
# Transition between second and third city
trans2 = z3.Or([z3.And(second == a, third == b) for a, b in allowed_transitions])
s.add(trans1, trans2)

if s.check() == z3.sat:
    model = s.model()
    first_val = model[first].as_long()
    second_val = model[second].as_long()
    third_val = model[third].as_long()
    
    # Map city codes to names and durations
    city_names = {0: 'Vilnius', 1: 'Munich', 2: 'Mykonos'}
    durations = []
    for city in [first_val, second_val, third_val]:
        if city == 0:
            durations.append(4)
        elif city == 1:
            durations.append(3)
        elif city == 2:
            durations.append(7)
    
    # Calculate day ranges
    start1 = 1
    end1 = start1 + durations[0] - 1
    start2 = end1
    end2 = start2 + durations[1] - 1
    start3 = end2
    end3 = start3 + durations[2] - 1
    
    # Build itinerary
    itinerary = [
        {"day_range": f"Day {start1}-{end1}", "place": city_names[first_val]},
        {"day_range": f"Day {start2}-{end2}", "place": city_names[second_val]},
        {"day_range": f"Day {start3}-{end3}", "place": city_names[third_val]}
    ]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))