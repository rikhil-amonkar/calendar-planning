for day in range(total_days - 1):
    current_city = day_to_city[day]
    next_city = day_to_city[day + 1]
    solver.add(Or(
        current_city == next_city,
        *[And(current_city == c1, next_city == c2) for (c1, c2) in allowed_transitions]
    ))