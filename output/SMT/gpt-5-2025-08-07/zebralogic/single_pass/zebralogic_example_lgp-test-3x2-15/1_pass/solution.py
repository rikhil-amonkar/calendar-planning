from z3 import Ints, Solver, Distinct, And, Abs
import json

# Create position variables for each Name (house numbers 1..3)
pos_Arnold, pos_Peter, pos_Eric = Ints('pos_Arnold pos_Peter pos_Eric')

# Create position variables for each Height (house numbers 1..3)
pos_short, pos_average, pos_very_short = Ints('pos_short pos_average pos_very_short')

s = Solver()

# Domain constraints: all positions are in 1..3
def in_domain(*vars_):
    return And(*[(v >= 1) & (v <= 3) for v in vars_])

s.add(in_domain(pos_Arnold, pos_Peter, pos_Eric,
                pos_short, pos_average, pos_very_short))

# All-different constraints within each category
s.add(Distinct(pos_Arnold, pos_Peter, pos_Eric))
s.add(Distinct(pos_short, pos_average, pos_very_short))

# Clue 1: Peter is somewhere to the right of Eric.
s.add(pos_Peter > pos_Eric)

# Clue 2: The person who is short is in the first house.
s.add(pos_short == 1)

# Clue 3: There is one house between the person who is short and the person who is very short.
s.add(Abs(pos_short - pos_very_short) == 2)

# Clue 4: Arnold and the person who is very short are next to each other.
s.add(Abs(pos_Arnold - pos_very_short) == 1)

assert s.check().r == 1, "No solution found."

m = s.model()

# Extract positions
name_positions = {
    "Arnold": m.evaluate(pos_Arnold, model_completion=True).as_long(),
    "Peter": m.evaluate(pos_Peter, model_completion=True).as_long(),
    "Eric": m.evaluate(pos_Eric, model_completion=True).as_long(),
}
height_positions = {
    "short": m.evaluate(pos_short, model_completion=True).as_long(),
    "average": m.evaluate(pos_average, model_completion=True).as_long(),
    "very short": m.evaluate(pos_very_short, model_completion=True).as_long(),
}

# Invert mappings: for each house, find name and height
rows = []
for house in [1, 2, 3]:
    name = next(n for n, p in name_positions.items() if p == house)
    height = next(h for h, p in height_positions.items() if p == house)
    rows.append([str(house), name, height])

output = {
    "solution": {
        "header": ["House", "Name", "Height"],
        "rows": rows
    }
}

print(json.dumps(output))