# Replace the duration_prev calculation in the loop
for i in range(1, 7):
    prev_city = order[i - 1]
    duration_prev = If(prev_city == 0, 3,
                       If(prev_city == 1, 2,
                          If(prev_city == 2, 5,
                             If(prev_city == 3, 3,
                                If(prev_city == 4, 5,
                                   If(prev_city == 5, 5,
                                      If(prev_city == 6, 5, 0)))))))
    solver.add(start_days[i] == start_days[i - 1] + duration_prev - 1)

# Replace the duration_last calculation
last_city = order[6]
duration_last = If(last_city == 0, 3,
                   If(last_city == 1, 2,
                      If(last_city == 2, 5,
                         If(last_city == 3, 3,
                            If(last_city == 4, 5,
                               If(last_city == 5, 5,
                                  If(last_city == 6, 5, 0)))))))
end_day_last = start_days[6] + duration_last - 1
solver.add(end_day_last == 22)