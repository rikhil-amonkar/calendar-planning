for i in locations:
    for j in locations:
        if i!= j:
            solver.add(visit_times[i] + reverse_travel_times[i][j] <= visit_times[j])