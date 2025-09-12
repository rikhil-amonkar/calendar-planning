import z3

# End day for each city is start + duration - 1
for i in range(6):
    duration = (
        z3.If(cities_order[i] == 0, 3,
              z3.If(cities_order[i] == 1, 2,
                    z3.If(cities_order[i] == 2, 3,
                          z3.If(cities_order[i] == 3, 2,
                                z3.If(cities_order[i] == 4, 3, 5)))))
    )
    s.add(end_days[i] == start_days[i] + duration - 1)