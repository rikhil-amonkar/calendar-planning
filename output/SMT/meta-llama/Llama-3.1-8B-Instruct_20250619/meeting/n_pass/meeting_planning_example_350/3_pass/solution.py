for i in betty_time_slot:
    if betty_time_slot[i]!= bayview:
        solver.add(And(x[betty_time_slot[i]], y[betty_time_slot[i]]) == Implies(x[betty_time_slot[i]], y[betty_time_slot[i]]) == Or([And(x[betty_time_slot[i]], y[betty_time_slot[i]]) == Implies(x[betty_time_slot[i]], y[betty_time_slot[i]]) == t >= 9 + i for t in range(9 + i, 9 + i + 10)]))

for i in charles_time_slot:
    if charles_time_slot[i]!= bayview:
        solver.add(And(x[charles_time_slot[i]], y[charles_time_slot[i]]) == Implies(x[charles_time_slot[i]], y[charles_time_slot[i]]) == Or([And(x[charles_time_slot[i]], y[charles_time_slot[i]]) == Implies(x[charles_time_slot[i]], y[charles_time_slot[i]]) == t >= 540 + 11.25 + i for t in range(int(540 + 11.25 + i), int(540 + 11.25 + i + 3.25 * 60))]))