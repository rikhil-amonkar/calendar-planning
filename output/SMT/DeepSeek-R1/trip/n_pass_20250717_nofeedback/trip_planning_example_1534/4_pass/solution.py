import z3

def main():
    n = 10
    total_days = 25

    city_names = ["Paris", "Florence", "Barcelona", "Tallinn", "Amsterdam", "Vilnius", "Warsaw", "Venice", "Hamburg", "Salzburg"]
    min_days = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    max_days = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

    assign = [z3.Int(f"assign_{i}") for i in range(n)]
    d = [z3.Int(f"d_{i}") for i in range(n)]
    start = [z3.Int(f"start_{i}") for i in range(n)]
    end = [z3.Int(f"end_{i}") for i in range(n)]

    s = z3.Solver()

    for i in range(n):
        s.add(assign[i] >= 0, assign[i] < n)
    s.add(z3.Distinct(assign))

    s.add(start[0] == 1)
    for i in range(n-1):
        s.add(end[i] == start[i] + d[i] - 1)
        s.add(start[i+1] == end[i] + 1)
    s.add(end[n-1] == start[n-1] + d[n-1] - 1)
    s.add(end[n-1] == total_days)

    s.add(sum(d) == total_days)

    for i in range(n):
        or_constraints = []
        for k in range(n):
            or_constraints.append(z3.And(assign[i] == k, d[i] >= min_days[k], d[i] <= max_days[k]))
        s.add(z3.Or(or_constraints))

    for i in range(n):
        s.add(start[i] >= 1, start[i] <= total_days)
        s.add(end[i] >= 1, end[i] <= total_days)
        s.add(d[i] >= 1, d[i] <= 5)

    if s.check() == z3.sat:
        model = s.model()
        order = [model.eval(assign[i]).as_long() for i in range(n)]
        starts = [model.eval(start[i]).as_long() for i in range(n)]
        ends = [model.eval(end[i]).as_long() for i in range(n)]

        itinerary = []
        for i in range(n):
            city_index = order[i]
            city = city_names[city_index]
            s_day = starts[i]
            e_day = ends[i]
            if s_day == e_day:
                day_range = f"Day {s_day}"
            else:
                day_range = f"Day {s_day}-{e_day}"
            itinerary.append({'day_range': day_range, 'place': city})

        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()