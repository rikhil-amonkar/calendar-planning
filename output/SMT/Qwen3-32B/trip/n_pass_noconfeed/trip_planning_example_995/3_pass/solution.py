# For each city in the order, compute duration and add constraints
for i in range(7):
    duration = If(c[i] == Barcelona, 3,
            If(c[i] == Brussels, 3,
            If(c[i] == Copenhagen, 3,
            If(c[i] == Oslo, 2,
            If(c[i] == Split, 4,
            If(c[i] == Stuttgart, 3, 4))))))  # Removed one closing parenthesis
    end_day = start_days[i] + duration - 1
    if i < 6:
        s.add(start_days[i+1] == end_day)