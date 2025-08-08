import z3

def main():
    n = 10
    total_days = 25
    travel_days = n - 1
    city_days = total_days - travel_days

    city_names = ["Paris", "Florence", "Barcelona", "Tallinn", "Amsterdam", "Vilnius", "Warsaw", "Venice", "Hamburg", "Salzburg"]
    min_days = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    max_days = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

    assign = [z3.Int(f"assign_{i}") for i in range(n)]
    d = [z3.Int(f"d_{i}") for i in range(n)]

    s = z3.Solver()

    for i in range(n):
        s.add(assign[i] >= 0, assign[i] < n)
    s.add(z3.Distinct(assign))

    for i in range(n):
        or_constraints = []
        for k in range(n):
            or_constraints.append(z3.And(assign[i] == k, d[i] >= min_days[k], d[i] <= max_days[k]))
        s.add(z3.Or(or_constraints))

    s.add(sum(d) == city_days)

    if s.check() == z3.sat:
        model = s.model()
        order = [model.eval(assign[i]).as_long() for i in range(n)]
        durations = [model.eval(d[i]).as_long() for i in range(n)]

        cumulative_durations = 0
        itinerary = []
        for i in range(n):
            city_index = order[i]
            city = city_names[city_index]
            start_day = 1 + cumulative_durations + i
            end_day = start_day + durations[i] - 1
            cumulative_durations += durations[i]

            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({'day_range': day_range, 'place': city})

        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()