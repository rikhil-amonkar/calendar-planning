from z3 import *

city_names = ['Reykjavik', 'Stuttgart', 'Manchester', 'Istanbul', 'Riga', 'Bucharest', 'Vienna', 'Florence']
min_days = [2, 3, 2, 2, 2, 3, 2, 3]
max_days = [4, 5, 3, 3, 3, 4, 3, 4]

graph = {
    'Reykjavik': ['Vienna', 'Stuttgart', 'Manchester', 'Florence', 'Istanbul', 'Riga', 'Bucharest'],
    'Stuttgart': ['Reykjavik', 'Manchester', 'Florence', 'Istanbul', 'Riga', 'Bucharest'],
    'Manchester': ['Reykjavik', 'Stuttgart', 'Florence', 'Istanbul', 'Riga', 'Bucharest'],
    'Istanbul': ['Reykjavik', 'Stuttgart', 'Manchester', 'Florence', 'Riga', 'Bucharest'],
    'Riga': ['Reykjavik', 'Stuttgart', 'Manchester', 'Florence', 'Istanbul', 'Bucharest'],
    'Bucharest': ['Reykjavik', 'Stuttgart', 'Manchester', 'Florence', 'Istanbul', 'Riga'],
    'Vienna': ['Reykjavik', 'Florence'],
    'Florence': ['Reykjavik', 'Stuttgart', 'Manchester', 'Istanbul', 'Riga', 'Bucharest', 'Vienna']
}

allowed_set = set()
for idx, city in enumerate(city_names):
    for neighbor in graph[city]:
        j = city_names.index(neighbor)
        allowed_set.add((idx, j))

s = Solver()
s.set("smt.random_seed", 123)
s.set("sat.random_seed", 123)

itinerary = [Int(f"itinerary_{i}") for i in range(8)]
for i in range(8):
    s.add(itinerary[i] >= 0, itinerary[i] < 8)
s.add(Distinct(itinerary))

start_day = [Int(f"start_{i}") for i in range(8)]
end_day = [Int(f"end_{i}") for i in range(8)]

s.add(start_day[0] == 1)
s.add(end_day[7] == 23)

for i in range(7):
    s.add(end_day[i] + 1 == start_day[i+1])

for i in range(8):
    stay_days_i = Int(f"stay_days_{i}")
    s.add(stay_days_i == end_day[i] - start_day[i] + 1)
    
    conds = []
    for j in range(8):
        c = And(itinerary[i] == j, stay_days_i >= min_days[j], stay_days_i <= max_days[j])
        conds.append(c)
    s.add(Or(conds))

for i in range(7):
    c1 = itinerary[i]
    c2 = itinerary[i+1]
    disj = False
    for (a, b) in allowed_set:
        disj = Or(disj, And(c1 == a, c2 == b))
    s.add(disj)

if s.check() == sat:
    model = s.model()
    order = [model.evaluate(itinerary[i]).as_long() for i in range(8)]
    starts = [model.evaluate(start_day[i]).as_long() for i in range(8)]
    ends = [model.evaluate(end_day[i]).as_long() for i in range(8)]
    
    plan = []
    for i in range(8):
        city_index = order[i]
        city = city_names[city_index]
        s_day = starts[i]
        e_day = ends[i]
        if s_day == e_day:
            day_range = f"Day {s_day}"
        else:
            day_range = f"Day {s_day}-{e_day}"
        plan.append({'day_range': day_range, 'place': city})
    
    result = {'itinerary': plan}
    print(f"Plan found: {result}")
else:
    print("No valid plan found.")