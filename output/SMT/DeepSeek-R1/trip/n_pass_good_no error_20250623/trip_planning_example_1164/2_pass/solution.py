from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    reqs = [2, 2, 5, 3, 4, 3, 3, 2]  # Corresponding to the cities list

    city_to_index = {city: idx for idx, city in enumerate(cities)}

    edges = [
        ('Copenhagen', 'Vienna'),
        ('Nice', 'Stockholm'),
        ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'),
        ('Nice', 'Porto'),
        ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'),
        ('Nice', 'Venice'),
        ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'),
        ('Nice', 'Copenhagen'),
        ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'),
        ('Copenhagen', 'Porto'),
        ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Vienna'),
        ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto')
    ]

    adj_set = [set() for _ in range(8)]
    for a, b in edges:
        i = city_to_index[a]
        j = city_to_index[b]
        adj_set[i].add(j)
        adj_set[j].add(i)

    seq = IntVector('seq', 8)
    start_day = IntVector('start_day', 8)
    end_day = IntVector('end_day', 8)

    s = Solver()

    for i in range(8):
        s.add(seq[i] >= 0, seq[i] < 8)
    s.add(Distinct(seq))

    for k in range(7):
        cond = False
        for i in range(8):
            for j in adj_set[i]:
                cond = Or(cond, And(seq[k] == i, seq[k+1] == j))
        s.add(cond)

    s.add(start_day[0] == 1)
    s.add(end_day[7] == 17)

    for k in range(7):
        s.add(end_day[k] == start_day[k+1])

    for k in range(8):
        cond = False
        for i in range(8):
            cond = Or(cond, And(seq[k] == i, end_day[k] - start_day[k] + 1 == reqs[i]))
        s.add(cond)

    for k in range(8):
        s.add(Implies(seq[k] == 0, And(start_day[k] <= 3, end_day[k] >= 3)))  # Reykjavik must include day 3
        s.add(Implies(seq[k] == 1, And(start_day[k] <= 4, end_day[k] >= 4)))  # Stockholm must include day 4
        s.add(Implies(seq[k] == 2, end_day[k] >= 13))  # Porto must end on or after day 13
        s.add(Implies(seq[k] == 5, And(start_day[k] <= 13, end_day[k] >= 11)))  # Vienna must overlap [11,13]
        s.add(start_day[k] >= 1, start_day[k] <= 17)
        s.add(end_day[k] >= 1, end_day[k] <= 17)
        s.add(end_day[k] >= start_day[k])

    if s.check() == sat:
        m = s.model()
        seq_val = [m[seq[i]].as_long() for i in range(8)]
        start_val = [m[start_day[i]].as_long() for i in range(8)]
        end_val = [m[end_day[i]].as_long() for i in range(8)]

        itinerary = []
        for k in range(8):
            city_name = cities[seq_val[k]]
            s_val = start_val[k]
            e_val = end_val[k]
            itinerary.append({"day_range": f"Day {s_val}-{e_val}", "place": city_name})
            if k < 7:
                itinerary.append({"day_range": f"Day {e_val}", "place": city_name})
                next_city = cities[seq_val[k+1]]
                itinerary.append({"day_range": f"Day {e_val}", "place": next_city})

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()