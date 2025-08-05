import z3
import json

City, (Reykjavik, Stockholm, Oslo, Tallinn, Stuttgart, Split, Geneva, Porto) = \
    z3.EnumSort('City', ['Reykjavik', 'Stockholm', 'Oslo', 'Tallinn', 'Stuttgart', 'Split', 'Geneva', 'Porto'])

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

c = [z3.Const(f'c_{i}', City) for i in range(21)]

solver = z3.Solver()

starts = [Reykjavik] + c[:20]
ends = c

for i in range(21):
    options = [starts[i] == ends[i]]
    for (a, b) in allowed_pairs:
        options.append(z3.And(starts[i] == a, ends[i] == b))
    solver.add(z3.Or(options))

solver.add(ends[18] == Porto)
solver.add(ends[19] == Porto)
solver.add(ends[20] == Porto)

solver.add(z3.Or(starts[1] == Reykjavik, ends[1] == Reykjavik))

presence_day2 = z3.Or(starts[1] == Stockholm, ends[1] == Stockholm)
presence_day3 = z3.Or(starts[2] == Stockholm, ends[2] == Stockholm)
presence_day4 = z3.Or(starts[3] == Stockholm, ends[3] == Stockholm)
solver.add(z3.Or(presence_day2, presence_day3, presence_day4))

def total_days(city):
    total = 0
    for i in range(21):
        total += z3.If(z3.Or(starts[i] == city, ends[i] == city), 1, 0)
    return total

solver.add(total_days(Reykjavik) == 2)
solver.add(total_days(Oslo) == 5)
solver.add(total_days(Stuttgart) == 5)
solver.add(total_days(Split) == 3)
solver.add(total_days(Geneva) == 2)
solver.add(total_days(Porto) == 3)
solver.add(total_days(Tallinn) == 5)
solver.add(total_days(Stockholm) == 3)

if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(21):
        start_val = model.eval(starts[i])
        end_val = model.eval(ends[i])
        if start_val.eq(end_val):
            cities = [str(start_val)]
        else:
            cities = sorted([str(start_val), str(end_val)])
        itinerary.append({"day": i+1, "city": cities})
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))