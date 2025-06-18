from z3 import *

def main():
    # City indices
    dublin = 0
    madrid = 1
    oslo = 2
    london = 3
    vilnius = 4
    berlin = 5

    cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
    dur = [3, 2, 3, 2, 3, 5]

    edges_undirected = [
        (dublin, madrid), (dublin, oslo), (dublin, london), (dublin, berlin),
        (madrid, oslo), (madrid, london), (madrid, berlin),
        (oslo, london), (oslo, vilnius), (oslo, berlin),
        (london, berlin),
        (vilnius, berlin)
    ]

    edges_list = []
    for (i, j) in edges_undirected:
        edges_list.append((i, j))
        edges_list.append((j, i))

    s = Solver()

    pos = [Int(f'pos_{i}') for i in range(6)]
    for i in range(6):
        s.add(pos[i] >= 0, pos[i] < 6)
    s.add(Distinct(pos))

    for k in range(5):
        cons_expr = []
        for (i, j) in edges_list:
            cons_expr.append(And(pos[i] == k, pos[j] == k+1))
        s.add(Or(cons_expr))

    start_days = [Int(f'start_{i}') for i in range(6)]
    for i in range(6):
        sum_expr = Sum([If(pos[j] < pos[i], dur[j], 0) for j in range(6)])
        s.add(start_days[i] == 1 - pos[i] + sum_expr)

    s.add(start_days[dublin] >= 5)
    s.add(start_days[dublin] <= 9)
    s.add(start_days[madrid] >= 1)
    s.add(start_days[madrid] <= 3)
    s.add(start_days[berlin] >= 1)
    s.add(start_days[berlin] <= 7)

    if s.check() == sat:
        model = s.model()
        pos_vals = [model.evaluate(pos[i]).as_long() for i in range(6)]
        start_vals = [model.evaluate(start_days[i]).as_long() for i in range(6)]

        order = sorted(range(6), key=lambda i: pos_vals[i])
        itinerary = []
        for idx, city_idx in enumerate(order):
            start = start_vals[city_idx]
            d = dur[city_idx]
            end = start + d - 1
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": cities[city_idx]
            })
            if idx < 5:
                next_city_idx = order[idx+1]
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": cities[city_idx]
                })
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": cities[next_city_idx]
                })
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()